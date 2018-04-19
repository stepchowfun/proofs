FROM debian:stretch

RUN \
  DEBIAN_FRONTEND=noninteractive apt-get -y update && \
  DEBIAN_FRONTEND=noninteractive apt-get -y install \
    'build-essential=12.3' \
    'ruby=1:2.3.*' && \
  rm -rf /var/lib/apt/lists/*

RUN \
  DEBIAN_FRONTEND=noninteractive apt-get -y update && \
  DEBIAN_FRONTEND=noninteractive apt-get -y install \
    'camlp5=6.16-*' \
    'curl=7.52.*' \
    'ocaml=4.02.*' && \
  rm -rf /var/lib/apt/lists/* && \
  curl -fsSLo coq.tar.gz https://github.com/coq/coq/archive/V8.8.0.tar.gz && \
  tar -xzf coq.tar.gz && \
  rm coq.tar.gz && \
  cd coq-8.8.0 && \
  ./configure -prefix /usr/local && \
  make && \
  make install && \
  cd .. && \
  rm -rf coq-8.8.0 && \
  DEBIAN_FRONTEND=noninteractive apt-get -y purge --auto-remove \
    'camlp5' \
    'curl' \
    'ocaml'

RUN useradd --user-group --create-home user

USER user:user

WORKDIR /home/user

RUN echo 'export LANG="C.UTF-8"' >> ~/.profile
