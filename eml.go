// Based on: https://github.com/k3a/parsemail/blob/master/parsemail.go
package emlparser

import (
	"bufio"
	"bytes"
	"encoding/base64"
	"fmt"
	"io"
	"mime"
	"mime/multipart"
	"mime/quotedprintable"
	"net/mail"
	"regexp"
	"slices"
	"strings"
	"time"
	"unicode"

	"github.com/gogs/chardet"
	"golang.org/x/text/encoding"
	"golang.org/x/text/encoding/htmlindex"
)

// MIME content types used in emails.
const (
	contentTypeMultipartMixed       = "multipart/mixed"
	contentTypeMultipartAlternative = "multipart/alternative"
	contentTypeMultipartRelated     = "multipart/related"
	contentTypeTextHtml             = "text/html"
	contentTypeTextPlain            = "text/plain"
	contentTypeOctetStream          = "application/octet-stream"
)

// Email with fields for all the headers defined in RFC5322 with it's attachments and
type Email struct {
	Header          mail.Header
	Subject         string
	Sender          *mail.Address
	From            []*mail.Address
	ReplyTo         []*mail.Address
	To              []*mail.Address
	Cc              []*mail.Address
	Bcc             []*mail.Address
	Date            time.Time
	MessageId       string
	InReplyTo       []string
	References      []string
	ResentFrom      []*mail.Address
	ResentSender    *mail.Address
	ResentTo        []*mail.Address
	ResentDate      time.Time
	ResentCc        []*mail.Address
	ResentBcc       []*mail.Address
	ResentMessageId string
	ContentType     string
	Content         io.Reader
	BodyHtml        string
	BodyText        string
	Attachments     []Attachment
	EmbeddedFiles   []EmbeddedFile
}

// Attachment with filename, content type and data (as a io.Reader)
type Attachment struct {
	Filename    string
	MediaType   string
	ContentType string
	Data        io.Reader
}

// EmbeddedFile with content id, content type and data (as a io.Reader)
type EmbeddedFile struct {
	Cid         string
	MediaType   string
	ContentType string
	Data        io.Reader
}

type headerParser struct {
	header *mail.Header
	err    error
}

type strip struct {
	br              *bufio.Reader
	headerBuffer    *bytes.Buffer
	headerComplete  bool
	cleanHeaderSent bool
	headerStarted   bool
}

var (
	reFrom       = regexp.MustCompile(`(?m)^>+\s*From\s+`)
	reDecodeMime = regexp.MustCompile(`=\?(.+?)\?(.)\?(.+?)\?=`)
)

// Parse an email message read from io.Reader into parsemail.Email struct
func Parse(r io.Reader) (email Email, err error) {
	msg, err := mail.ReadMessage(&strip{
		br:              bufio.NewReader(r),
		headerBuffer:    &bytes.Buffer{},
		headerComplete:  false,
		cleanHeaderSent: false,
		headerStarted:   false,
	})

	if err != nil {
		return
	}

	email, err = createEmailFromHeader(msg.Header)
	if err != nil {
		return
	}

	email.ContentType = msg.Header.Get("Content-Type")
	if len(email.ContentType) > 0 {
		var ctp []string
		var tmp []string
		for _, p := range strings.Split(email.ContentType, ";") {
			pl := strings.ToLower(strings.TrimSpace(p))
			if !slices.Contains(tmp, pl) {
				tmp = append(tmp, pl)
				ctp = append(ctp, strings.TrimSpace(p))
			}
		}

		email.ContentType = strings.Join(ctp, "; ")
	}

	contentType, params, err := parseContentType(email.ContentType)
	if err != nil {
		if len(contentType) == 0 || (contentType != contentTypeTextPlain && contentType != contentTypeTextHtml) {
			return
		}
	}

	cte := msg.Header.Get("Content-Transfer-Encoding")

	switch contentType {
	case contentTypeMultipartMixed:
		email.BodyText, email.BodyHtml, email.Attachments, email.EmbeddedFiles, err = parseMultipartMixed(msg.Body, params["boundary"])
	case contentTypeMultipartAlternative:
		email.BodyText, email.BodyHtml, email.EmbeddedFiles, err = parseMultipartAlternative(msg.Body, params["boundary"])
	case contentTypeMultipartRelated:
		email.BodyText, email.BodyHtml, email.EmbeddedFiles, err = parseMultipartRelated(msg.Body, params["boundary"])
	case contentTypeTextPlain:
		var reader io.Reader
		var prms map[string]string
		var charset string

		_, prms, err = parseContentType(msg.Header.Get("Content-Type"))
		if err == nil {
			charset = getCharset(prms)
		}

		message, _ := io.ReadAll(msg.Body)
		reader, err = decodeContent(strings.NewReader(string(message[:])), cte, charset, false)
		if err != nil {
			return
		}

		message, err = io.ReadAll(reader)
		if err != nil {
			return
		}

		email.BodyText = strings.TrimSuffix(string(message[:]), "\n")
	case contentTypeTextHtml:
		var reader io.Reader
		var prms map[string]string
		var charset string

		_, prms, err = parseContentType(msg.Header.Get("Content-Type"))
		if err == nil {
			charset = getCharset(prms)
		}

		message, _ := io.ReadAll(msg.Body)
		reader, err = decodeContent(bytes.NewReader(message), cte, charset, false)
		if err != nil {
			return
		}

		message, err = io.ReadAll(reader)
		if err != nil {
			return
		}

		email.BodyHtml = strings.TrimSuffix(string(message[:]), "\n")
	case contentTypeOctetStream:
		email.Attachments, err = parseAttachmentOnlyEmail(msg.Body, msg.Header)
	default:
		email.Content, err = decodeContent(msg.Body, cte, "", false)
	}

	return
}

func (st *strip) Read(p []byte) (int, error) {
	if !st.headerComplete {
		err := st.readHeader()
		if err != nil && err != io.EOF {
			return 0, err
		}
	}

	if !st.cleanHeaderSent {
		return st.sendCleanHeader(p)
	}

	return st.br.Read(p)
}

func (st *strip) readHeader() error {
	for {
		r, _, err := st.br.ReadRune()
		if err != nil {
			if err == io.EOF {
				st.headerComplete = true
				return nil
			}

			return err
		}

		if !st.headerStarted && unicode.IsSpace(r) {
			continue // Skip leading whitespace
		}

		st.headerStarted = true
		st.headerBuffer.WriteRune(r)

		if r == '\n' {
			nextRune, _, err := st.br.ReadRune()
			if err != nil {
				if err == io.EOF {
					st.headerComplete = true
					return nil
				}
				return err
			}

			st.headerBuffer.WriteRune(nextRune)

			if nextRune == '\n' || (nextRune == '\r' && st.peekNewline()) {
				st.headerComplete = true
				return nil
			}
		}
	}
}

func (st *strip) peekNewline() bool {
	nextByte, err := st.br.Peek(1)
	if err != nil {
		return false
	}

	return nextByte[0] == '\n'
}

func (st *strip) sendCleanHeader(p []byte) (int, error) {
	cleanHeader := reFrom.ReplaceAll(st.headerBuffer.Bytes(), []byte{})
	n := copy(p, cleanHeader)
	if n < len(cleanHeader) {
		st.headerBuffer = bytes.NewBuffer(cleanHeader[n:])
	} else {
		st.cleanHeaderSent = true
	}

	return n, nil
}

func createEmailFromHeader(header mail.Header) (Email, error) {
	hp := headerParser{header: &header}
	email := Email{
		Subject:         decodeMimeSentence(header.Get("Subject")),
		From:            hp.parseAddressList(header.Get("From")),
		Sender:          hp.parseAddress(header.Get("Sender")),
		ReplyTo:         hp.parseAddressList(header.Get("Reply-To")),
		To:              hp.parseAddressList(header.Get("To")),
		Cc:              hp.parseAddressList(header.Get("Cc")),
		Bcc:             hp.parseAddressList(header.Get("Bcc")),
		Date:            hp.parseTime(header.Get("Date")),
		ResentFrom:      hp.parseAddressList(header.Get("Resent-From")),
		ResentSender:    hp.parseAddress(header.Get("Resent-Sender")),
		ResentTo:        hp.parseAddressList(header.Get("Resent-To")),
		ResentCc:        hp.parseAddressList(header.Get("Resent-Cc")),
		ResentBcc:       hp.parseAddressList(header.Get("Resent-Bcc")),
		ResentMessageId: hp.parseMessageId(header.Get("Resent-Message-ID")),
		MessageId:       hp.parseMessageId(header.Get("Message-ID")),
		InReplyTo:       hp.parseMessageIdList(header.Get("In-Reply-To")),
		References:      hp.parseMessageIdList(header.Get("References")),
		ResentDate:      hp.parseTime(header.Get("Resent-Date")),
	}

	if hp.err != nil {
		return email, hp.err
	}

	// Decode whole header for easier access to extra fields
	var err error
	email.Header, err = decodeHeaderMime(header)
	if err != nil {
		return email, err
	}

	return email, err
}

func parseAttachmentOnlyEmail(body io.Reader, header mail.Header) ([]Attachment, error) {
	var attachments []Attachment

	contentDisposition := header.Get("Content-Disposition")

	if len(contentDisposition) > 0 && strings.Contains(contentDisposition, "attachment;") {
		attachmentData, err := decodeContent(body, header.Get("Content-Transfer-Encoding"), "", true)
		if err != nil {
			return attachments, err
		}

		fileName := strings.Replace(contentDisposition, "attachment; filename=\"", "", -1)
		fileName = strings.TrimRight(fileName, "\"")

		attachments = append(attachments, Attachment{
			Filename:    fileName,
			MediaType:   "application/octet-stream",
			ContentType: header.Get("Content-Type"),
			Data:        attachmentData,
		})
	}

	return attachments, nil
}

func parseMultipartRelated(msg io.Reader, boundary string) (textBody, htmlBody string, embeddedFiles []EmbeddedFile, err error) {
	pmr := multipart.NewReader(msg, boundary)
	for {
		part, err := pmr.NextRawPart()

		if err == io.EOF {
			break
		} else if err != nil {
			return textBody, htmlBody, embeddedFiles, err
		}

		contentType, params, err := mime.ParseMediaType(part.Header.Get("Content-Type"))
		if err != nil {
			return textBody, htmlBody, embeddedFiles, err
		}

		cte := part.Header.Get("Content-Transfer-Encoding")

		switch contentType {
		case contentTypeTextPlain:
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			textBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		case contentTypeTextHtml:
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			htmlBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		case contentTypeMultipartAlternative:
			tb, hb, ef, err := parseMultipartAlternative(part, params["boundary"])
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			htmlBody += hb
			textBody += tb
			embeddedFiles = append(embeddedFiles, ef...)
		default:
			if isEmbeddedFile(part) {
				ef, err := decodeEmbeddedFile(part)
				if err != nil {
					return textBody, htmlBody, embeddedFiles, err
				}

				embeddedFiles = append(embeddedFiles, ef)
			} else {
				return textBody, htmlBody, embeddedFiles, fmt.Errorf("can't process multipart/related inner mime type: %s", contentType)
			}
		}
	}

	return textBody, htmlBody, embeddedFiles, err
}

func parseMultipartAlternative(msg io.Reader, boundary string) (textBody, htmlBody string, embeddedFiles []EmbeddedFile, err error) {
	pmr := multipart.NewReader(msg, boundary)
	for {
		part, err := pmr.NextRawPart()

		if err == io.EOF {
			break
		} else if err != nil {
			return textBody, htmlBody, embeddedFiles, err
		}

		contentType, params, err := mime.ParseMediaType(part.Header.Get("Content-Type"))
		if err != nil {
			return textBody, htmlBody, embeddedFiles, err
		}

		cte := part.Header.Get("Content-Transfer-Encoding")

		switch contentType {
		case contentTypeTextPlain:
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			textBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		case contentTypeTextHtml:
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			htmlBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		case contentTypeMultipartRelated:
			tb, hb, ef, err := parseMultipartRelated(part, params["boundary"])
			if err != nil {
				return textBody, htmlBody, embeddedFiles, err
			}

			htmlBody += hb
			textBody += tb
			embeddedFiles = append(embeddedFiles, ef...)
		default:
			if isEmbeddedFile(part) {
				ef, err := decodeEmbeddedFile(part)
				if err != nil {
					return textBody, htmlBody, embeddedFiles, err
				}

				embeddedFiles = append(embeddedFiles, ef)
			} else {
				return textBody, htmlBody, embeddedFiles, fmt.Errorf("can't process multipart/alternative inner mime type: %s", contentType)
			}
		}
	}

	return textBody, htmlBody, embeddedFiles, err
}

func parseMultipartMixed(msg io.Reader, boundary string) (textBody, htmlBody string, attachments []Attachment, embeddedFiles []EmbeddedFile, err error) {
	mr := multipart.NewReader(msg, boundary)
	for {
		part, err := mr.NextRawPart()
		if err == io.EOF {
			break
		} else if err != nil {
			return textBody, htmlBody, attachments, embeddedFiles, err
		}

		if isAttachment(part) {
			at, err := decodeAttachment(part)
			if err != nil {
				if !strings.Contains(err.Error(), "illegal base64 data") {
					return textBody, htmlBody, attachments, embeddedFiles, err
				} else {
					continue
				}
			}

			attachments = append(attachments, at)
			continue
		}

		contentType, params, err := mime.ParseMediaType(part.Header.Get("Content-Type"))
		if err != nil {
			return textBody, htmlBody, attachments, embeddedFiles, err
		}

		if isAttachment(part) {
			at, err := decodeAttachment(part)
			if err != nil {
				if !strings.Contains(err.Error(), "illegal base64 data") {
					return textBody, htmlBody, attachments, embeddedFiles, err
				} else {
					continue
				}
			}
			attachments = append(attachments, at)
		}

		cte := part.Header.Get("Content-Transfer-Encoding")

		if contentType == contentTypeMultipartAlternative {
			textBody, htmlBody, embeddedFiles, err = parseMultipartAlternative(part, params["boundary"])
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}
		} else if contentType == contentTypeMultipartRelated {
			textBody, htmlBody, embeddedFiles, err = parseMultipartRelated(part, params["boundary"])
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}
		} else if contentType == contentTypeTextPlain {
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}

			textBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		} else if contentType == contentTypeTextHtml {
			decoded, err := decodeContent(part, cte, getCharset(params), false)
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}

			ppContent, err := io.ReadAll(decoded)
			if err != nil {
				return textBody, htmlBody, attachments, embeddedFiles, err
			}

			htmlBody += strings.TrimSuffix(string(ppContent[:]), "\n")
		} else {
			at, err := decodeAttachment(part)
			if err != nil {
				if !strings.Contains(err.Error(), "illegal base64 data") {
					return textBody, htmlBody, attachments, embeddedFiles, err
				} else {
					continue
				}
			}

			attachments = append(attachments, at)
		}
	}

	return textBody, htmlBody, attachments, embeddedFiles, err
}

func decodeMimeSentence(s string) string {
	dec := new(mime.WordDecoder)

	if sdec, err := dec.DecodeHeader(s); err == nil && len(sdec) > 0 {
		return sdec
	} else if len(s) > 0 {
		encoding, text := decodeMime(s)
		if enc, err := htmlindex.Get(encoding); err == nil && enc != nil {
			if sdec, err := enc.NewDecoder().String(text); err == nil && len(sdec) > 0 {
				return sdec
			}
		}

		return s
	}

	return ""
}

func decodeMime(s string) (string, string) {
	var encoding string
	var decoded string

	matches := reDecodeMime.FindAllStringSubmatchIndex(s, -1)

	if len(matches) > 0 {
		var index int
		var parts []string

		for _, m := range matches {
			if m[0] > index {
				parts = append(parts, s[index:m[0]])
			}

			fullMatch := s[m[0]:m[1]]
			encoding = strings.ToLower(s[m[2]:m[3]])
			method := strings.ToUpper(s[m[4]:m[5]])
			encodedText := s[m[6]:m[7]]

			var decodedPart string
			if method == "Q" {
				qp := quotedprintable.NewReader(strings.NewReader(encodedText))
				b, err := io.ReadAll(qp)
				if err == nil {
					decodedPart = string(b)
				}
			} else if method == "B" {
				decodedBytes, _ := base64.StdEncoding.DecodeString(encodedText)
				decodedPart = string(decodedBytes)
			} else {
				decodedPart = fullMatch
			}

			parts = append(parts, decodedPart)
			index = m[1]
		}

		if index < len(s) {
			parts = append(parts, s[index:])
		}

		decoded = strings.Join(parts, "")
	} else {
		decoded = s
	}

	return encoding, decoded
}

func decodeHeaderMime(header mail.Header) (mail.Header, error) {
	parsedHeader := map[string][]string{}

	for headerName, headerData := range header {
		parsedHeaderData := []string{}
		for _, headerValue := range headerData {
			parsedHeaderData = append(parsedHeaderData, decodeMimeSentence(headerValue))
		}

		parsedHeader[headerName] = parsedHeaderData
	}

	return mail.Header(parsedHeader), nil
}

func isEmbeddedFile(part *multipart.Part) bool {
	return part.Header.Get("Content-Transfer-Encoding") != ""
}

func decodeEmbeddedFile(part *multipart.Part) (EmbeddedFile, error) {
	var ef EmbeddedFile

	decoded, err := decodeContent(part, part.Header.Get("Content-Transfer-Encoding"), "", true)
	if err != nil {
		return ef, err
	}

	var mediaType string
	tmp := strings.Split(part.Header.Get("Content-Type"), ";")
	if len(tmp) > 0 {
		mediaType = tmp[0]
	}

	ef.Cid = strings.Trim(decodeMimeSentence(part.Header.Get("Content-Id")), "<>")
	ef.Data = decoded
	ef.MediaType = mediaType
	ef.ContentType = part.Header.Get("Content-Type")

	return ef, nil
}

func isAttachment(part *multipart.Part) bool {
	return part.FileName() != ""
}

func decodeAttachment(part *multipart.Part) (Attachment, error) {
	var at Attachment

	filename := decodeMimeSentence(part.FileName())
	decoded, err := decodeContent(part, part.Header.Get("Content-Transfer-Encoding"), "", true)
	if err != nil {
		return at, err
	}

	var mediaType string
	tmp := strings.Split(part.Header.Get("Content-Type"), ";")
	if len(tmp) > 0 {
		mediaType = tmp[0]
	}

	at.Filename = filename
	at.Data = decoded
	at.MediaType = mediaType
	at.ContentType = part.Header.Get("Content-Type")

	return at, nil
}

func decodeContent(content io.Reader, encoding string, charset string, isFile bool) (io.Reader, error) {
	switch strings.ToLower(encoding) {
	case "base64":
		decoded := base64.NewDecoder(base64.StdEncoding, content)

		if isFile {
			b, err := io.ReadAll(decoded)
			if err != nil {
				return nil, err
			}

			return bytes.NewReader(b), nil
		}

		return decodeWithCharset(base64.NewDecoder(base64.StdEncoding, content), charset)
		// The values "8bit", "7bit", and "binary" all imply that NO encoding has been performed and data need to be read as bytes.
		// "7bit" means that the data is all represented as short lines of US-ASCII data.
		// "8bit" means that the lines are short, but there may be non-ASCII characters (octets with the high-order bit set).
		// "Binary" means that not only may non-ASCII characters be present, but also that the lines are not necessarily short enough for SMTP transport.
	case "quoted-printable":
		b, err := io.ReadAll(quotedprintable.NewReader(content))
		if err != nil && (len(b) == 0 || !strings.Contains(err.Error(), "quotedprintable: invalid")) {
			return nil, err
		}

		return decodeWithCharset(bytes.NewReader(b), charset)
	case "", "7bit", "8bit", "binary":
		b, err := io.ReadAll(quotedprintable.NewReader(content))
		if isFile {
			if err != nil {
				return nil, err
			}

			return bytes.NewReader(b), nil
		}

		if err != nil && (len(b) == 0 || !strings.Contains(err.Error(), "quotedprintable: invalid")) {
			return decodeWithCharset(content, charset)
		}

		return decodeWithCharset(bytes.NewReader(b), charset)
	default:
		return nil, fmt.Errorf("unknown encoding: %s", encoding)
	}
}

func decodeWithCharset(r io.Reader, charset string) (io.Reader, error) {
	if charset != "" {
		if enc, err := htmlindex.Get(charset); err == nil && enc != nil {
			return enc.NewDecoder().Reader(r), nil
		}
	}

	b, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}

	if enc := detectEncoding(b); enc != nil {
		if db, err := enc.NewDecoder().Bytes(b); err == nil {
			return bytes.NewReader(db), nil
		}
	}

	return r, nil
}

func detectEncoding(buf []byte) encoding.Encoding {
	if res, err := chardet.NewTextDetector().DetectBest(buf); err == nil {
		if enc, err := htmlindex.Get(res.Charset); err == nil && enc != nil {
			return enc
		}
	}

	return nil
}

func (hp headerParser) parseAddress(s string) *mail.Address {
	var ma *mail.Address

	if hp.err != nil {
		return nil
	}

	if strings.Trim(s, " \n") != "" {
		if len(s) > 0 {
			if tmp := decodeMimeSentence(s); len(tmp) > 0 {
				s = tmp
			}

			ma, _ = mail.ParseAddress(s)
		}

		return ma
	}

	return nil
}

func (hp headerParser) parseAddressList(s string) []*mail.Address {
	var ma []*mail.Address

	if hp.err != nil {
		return ma
	}

	if strings.Trim(s, " \n") != "" {
		if len(s) > 0 {
			if tmp := decodeMimeSentence(s); len(tmp) > 0 {
				s = tmp
			}

			ma, _ = mail.ParseAddressList(s)
		}

		return ma
	}

	return ma
}

func (hp headerParser) parseTime(s string) time.Time {
	var t time.Time

	if hp.err != nil || s == "" {
		return t
	}

	formats := []string{
		time.RFC1123Z,
		"Mon, 2 Jan 2006 15:04:05 -0700",
		time.RFC1123Z + " (MST)",
		"Mon, 2 Jan 2006 15:04:05 -0700 (MST)",
		time.RFC822,
	}

	for _, format := range formats {
		if t, hp.err = time.Parse(format, s); hp.err == nil {
			return t
		}
	}

	return t
}

func (hp headerParser) parseMessageId(s string) string {
	if hp.err != nil {
		return ""
	}

	return strings.Trim(s, "<> ")
}

func (hp headerParser) parseMessageIdList(s string) []string {
	result := []string{}

	if hp.err != nil {
		return result
	}

	for _, p := range strings.Split(s, " ") {
		if strings.Trim(p, " \n") != "" {
			result = append(result, hp.parseMessageId(p))
		}
	}

	return result
}

func parseContentType(contentTypeHeader string) (string, map[string]string, error) {
	if contentTypeHeader == "" {
		return contentTypeTextPlain, map[string]string{}, nil
	}

	return mime.ParseMediaType(contentTypeHeader)
}

func getCharset(p map[string]string) string {
	if v, ok := p["charset"]; ok {
		return v
	}

	return ""
}
