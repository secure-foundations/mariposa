FROM rust:1.65-alpine3.15 AS build

ADD . build
RUN apk add --no-cache musl-dev
RUN cd build && cargo build --release

FROM alpine:3.15 AS final

COPY --from=build /build/target/release/mariposa /usr/bin/mariposa
ENTRYPOINT [ "/usr/bin/mariposa" ]
