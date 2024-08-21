# emlparser - simple email parsing Go library

> This package is based on [DusanKasan/parsemail](https://github.com/DusanKasan/parsemail) and [k3a/parsemail](https://github.com/k3a/parsemail).

This library allows for parsing an email message into a more convenient form than the `net/mail` provides. Where the `net/mail` just gives you a map of header fields and a `io.Reader` of its body, emlparser allows access to all the standard header fields set in [RFC5322](https://tools.ietf.org/html/rfc5322), html/text body as well as attachements/embedded content as binary streams with metadata.

## Simple usage

You just parse a io.Reader that holds the email data. The returned Email struct contains all the standard email information/headers as public fields.

```go
var reader io.Reader // this reads an email message
email, err := emlparser.Parse(reader) // returns Email struct and error
if err != nil {
    // handle error
}

fmt.Println(email.Subject)
fmt.Println(email.From)
fmt.Println(email.To)
fmt.Println(email.HTMLBody)
```

## Retrieving attachments

Attachments are a easily accessible as `Attachment` type, containing their mime type, filename and data stream.

```go
var reader io.Reader
email, err := emlparser.Parse(reader)
if err != nil {
    // handle error
}

for _, a := range(email.Attachments) {
    fmt.Println(a.Filename)
    fmt.Println(a.ContentType)
    //and read a.Data
}
```

## Retrieving embedded files

You can access embedded files in the same way you can access attachments. They contain the mime type, data stream and content id that is used to reference them through the email.

```go
var reader io.Reader
email, err := emlparser.Parse(reader)
if err != nil {
    // handle error
}

for _, a := range(email.EmbeddedFiles) {
    fmt.Println(a.CID)
    fmt.Println(a.ContentType)
    //and read a.Data
}
```

## Issues

Submit the [issues](https://github.com/attilabuti/emlparser/issues) if you find any bug or have any suggestion.

## Contribution

Fork the [repo](https://github.com/attilabuti/emlparser) and submit pull requests.

## License

This extension is licensed under the [MIT License](https://github.com/attilabuti/emlparser/blob/main/LICENSE).