FROM debian:stretch

RUN \
  DEBIAN_FRONTEND=noninteractive apt-get -y update && \
  DEBIAN_FRONTEND=noninteractive apt-get -y install \
    build-essential=12.3 \
    coq=8.6-4 && \
  rm -rf /var/lib/apt/lists/*

RUN useradd --user-group --create-home user

USER user:user

WORKDIR /home/user
