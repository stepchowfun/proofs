.PHONY: all main lint clean docker-deps docker-build

all: main lint

main:
	rm -f Makefile.coq _CoqProjectFull
	echo '-R coq Main' > _CoqProjectFull
	find coq -type f -name '*.v' >> _CoqProjectFull
	coq_makefile -f _CoqProjectFull -o Makefile.coq || \
	  (rm -f Makefile.coq _CoqProjectFull; exit 1)
	make -f Makefile.coq || \
	  (rm -f Makefile.coq _CoqProjectFull; exit 1)
	rm -f Makefile.coq _CoqProjectFull

lint:
	./scripts/general-lint.rb $(shell \
	  find . -type d \( \
	    -path ./.git \
	  \) -prune -o \( \
	    -name '*.rb' -o \
	    -name '*.sh' -o \
	    -name '*.v' -o \
	    -name '*.yml' -o \
	    -name 'Dockerfile' -o \
	    -name 'Makefile' \
	  \) -print \
	)

clean:
	rm -f _CoqProjectFull Makefile.coq \
	  $(shell \
	    find . -type f \( \
	      -name '*.glob' -o \
	      -name '*.v.d' -o \
	      -name '*.vo' -o \
	      -name '*.vo.aux' \
	    \) -print \
	  )

docker-deps:
	docker build -t stephanmisc/coq:8.6 scripts

docker-build:
	CONTAINER="$$( \
	  docker create --rm --user=root stephanmisc/coq:8.6 bash -c ' \
	    chown -R user:user repo && \
	    su user -s /bin/bash -l -c "cd repo && make clean && make" \
	  ' \
	)" && \
	docker cp . "$$CONTAINER:/home/user/repo" && \
	docker start --attach "$$CONTAINER"
