FROM debian:stretch
RUN \
  # Update package lists.
  DEBIAN_FRONTEND=noninteractive apt-get -y update && \

  # Install Make and Coq.
  DEBIAN_FRONTEND=noninteractive apt-get -y install build-essential coq && \

  # Free up some space by removing the package lists.
  rm -rf /var/lib/apt/lists/*
