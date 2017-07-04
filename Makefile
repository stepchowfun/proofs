# Phony targets

.PHONY: all lint clean docker-deps docker-build

all: \
  coq/intro.vo \
  coq/reflection.vo \
  coq/stlc.vo \
  lint

lint:
	./scripts/check-line-lengths.sh \
	  $(shell \
	    find . \
	      -type d \( \
	        -path ./.git \
	      \) -prune -o \
	      \( \
		-name '*.sh' -o \
		-name '*.v' -o \
		-name '*.yml' -o \
		-name 'Dockerfile' -o \
		-name 'Makefile' \
	      \) -print \
	  )

clean:
	rm -rf \
	  coq/*.glob \
	  coq/*.vo \
	  coq/.*.vo.aux

docker-deps:
	docker build -t stephanmisc/coq:4.6 .

docker-build:
	docker run \
	  --rm \
	  -v $$(pwd):/root \
	  stephanmisc/coq:4.6 \
	  sh -c 'cd /root && make'

# The Coq scripts

coq/intro.vo: coq/intro.v
	COQPATH="$$(pwd)" coqc coq/intro.v

coq/reflection.vo: coq/reflection.v
	COQPATH="$$(pwd)" coqc coq/reflection.v

coq/stlc.vo: coq/stlc.v
	COQPATH="$$(pwd)" coqc coq/stlc.v
