# Image of the ω = 6 search (notes/omega6-job.md). Build from the repository root:
#   docker build -f deploy/owf/Dockerfile -t <registry>/erdos-owf:<git-sha> .
# The node is arm64: build for linux/arm64 (e.g. `docker buildx build --platform linux/arm64 ...`).
FROM debian:bookworm-slim AS build
RUN apt-get update && apt-get install -y --no-install-recommends gcc libc6-dev libgmp-dev \
    && rm -rf /var/lib/apt/lists/*
COPY scripts/odd_weird_family.c /src/odd_weird_family.c
RUN gcc -O2 -Wall -o /owf /src/odd_weird_family.c -lgmp \
    && /owf 4 | grep -q '^4 True '

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends libgmp10 util-linux gzip coreutils gawk \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /owf /usr/local/bin/owf
COPY deploy/owf/run-root.sh /usr/local/bin/run-root.sh
# Seed for an empty volume only; afterwards the checkpoint in the volume is the source of truth.
COPY notes/data/omega6.ck.gz notes/data/omega6-2.ck.gz /opt/owf/seed/
RUN chmod 0755 /usr/local/bin/run-root.sh
USER 1000:1000
ENTRYPOINT ["/usr/local/bin/run-root.sh"]
