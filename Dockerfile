# syntax=docker/dockerfile:1
FROM golang:1.21-alpine

WORKDIR /app                  

COPY go.mod go.sum ./

RUN go mod download

COPY *.go ./

COPY static/ ./static

COPY schema.sql ./

RUN apk add --update gcc musl-dev

RUN CGO_ENABLED=1 go build -o statusnook \
    -ldflags "-w -s -X main.CA=https://acme-v02.api.letsencrypt.org/directory -X main.BUILD=release"


FROM alpine:latest     

WORKDIR /app         

COPY --from=0 /app ./

ENV PORT=8000

EXPOSE $PORT

CMD ["/bin/sh", "-c", "./statusnook -port $PORT -docker"]