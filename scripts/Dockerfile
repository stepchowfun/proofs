FROM debian:stretch

RUN \
  DEBIAN_FRONTEND=noninteractive apt-get -y update && \
  DEBIAN_FRONTEND=noninteractive apt-get -y install \
    build-essential \
    coq=8.6-4 && \
  rm -rf /var/lib/apt/lists/* && \
  useradd --user-group --create-home user
USER user:user
WORKDIR /home/user
