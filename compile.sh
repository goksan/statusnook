#!/bin/bash

CC=x86_64-linux-musl-gcc CXX=x86_64-linux-musl-g++ GOARCH=amd64 GOOS=linux CGO_ENABLED=1 go build -ldflags "-w -s -linkmode external -extldflags -static -X main.CA=https://acme-v02.api.letsencrypt.org/directory -X main.BUILD=release" -o bin/statusnook_linux_amd64_v0.1.0
CC=aarch64-linux-musl-gcc CXX=aarch64-linux-musl-g++ GOARCH=arm64 GOOS=linux CGO_ENABLED=1 go build -ldflags "-w -s -linkmode external -extldflags -static -X main.CA=https://acme-v02.api.letsencrypt.org/directory -X main.BUILD=release" -o bin/statusnook_linux_arm64_v0.1.0