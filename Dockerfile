# Build stage
FROM rust:1.85-slim-bookworm AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config \
    libssl-dev \
    git \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build
COPY Cargo.toml Cargo.lock* ./
COPY src/ src/
COPY benches/ benches/

RUN cargo build --release --bin rustdefend \
    && strip target/release/rustdefend

# Runtime stage
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libssl3 \
    git \
    && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home --shell /bin/bash rustdefend

COPY --from=builder /build/target/release/rustdefend /usr/local/bin/rustdefend

USER rustdefend
WORKDIR /workspace

ENTRYPOINT ["rustdefend"]

LABEL org.opencontainers.image.title="RustDefend" \
      org.opencontainers.image.description="Static security scanner for Rust smart contracts" \
      org.opencontainers.image.version="0.5.2" \
      org.opencontainers.image.authors="dehvCurtis" \
      org.opencontainers.image.url="https://github.com/0xStarBridge/RustDefend" \
      org.opencontainers.image.source="https://github.com/0xStarBridge/RustDefend" \
      org.opencontainers.image.licenses="MIT"
