FROM ghcr.io/xu-cheng/texlive-full@sha256:8b4a00b6a17ebe6b96dee107d82f0cb3eb40daf322f1e23809a9be26486963dd

ARG QUARTO_VERSION=1.9.37
ARG QUARTO_SHA256=78fcd90e983e3e7dbe3f0d1921cc10253c1eca7b92c20dd4bc2a3c1bca0a9af5
ARG NODE_VERSION=22.22.3
ARG NODE_SHA256=fc04ab27123cb34d2bca3416493e86ced2f81e1ab9b51e532721ed27a1ef677d

LABEL org.opencontainers.image.title="DossierRenderRuntime"
LABEL org.opencontainers.image.description="Pinned BEDC dossier render runtime"
LABEL org.opencontainers.image.source="https://github.com/the-omega-institute/newmath"
LABEL org.opencontainers.image.version="quarto-${QUARTO_VERSION}-node-${NODE_VERSION}-texlive-full"

ENV DEBIAN_FRONTEND=noninteractive
ENV PATH="/opt/quarto/bin:/opt/node/bin:${PATH}"

RUN if command -v apt-get >/dev/null 2>&1; then \
    apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl git xz-utils \
    && rm -rf /var/lib/apt/lists/*; \
  elif command -v apk >/dev/null 2>&1; then \
    apk add --no-cache ca-certificates curl git xz; \
  else \
    echo "no supported package manager found" >&2; exit 1; \
  fi

RUN curl -fsSL -o /tmp/quarto.tar.gz \
    "https://github.com/quarto-dev/quarto-cli/releases/download/v${QUARTO_VERSION}/quarto-${QUARTO_VERSION}-linux-amd64.tar.gz" \
  && echo "${QUARTO_SHA256}  /tmp/quarto.tar.gz" | sha256sum -c - \
  && mkdir -p /opt/quarto \
  && tar -xzf /tmp/quarto.tar.gz -C /opt/quarto --strip-components=1 \
  && rm /tmp/quarto.tar.gz

RUN curl -fsSL -o /tmp/node.tar.xz \
    "https://unofficial-builds.nodejs.org/download/release/v${NODE_VERSION}/node-v${NODE_VERSION}-linux-x64-musl.tar.xz" \
  && echo "${NODE_SHA256}  /tmp/node.tar.xz" | sha256sum -c - \
  && mkdir -p /opt/node \
  && tar -xJf /tmp/node.tar.xz -C /opt/node --strip-components=1 \
  && rm /tmp/node.tar.xz

COPY smoke.sh /usr/local/bin/dossier-render-smoke
RUN chmod +x /usr/local/bin/dossier-render-smoke \
  && /usr/local/bin/dossier-render-smoke
