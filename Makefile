.PHONY: main lint clean docker-deps docker-build

main:
	rm -f Makefile.coq _CoqProjectFull
	echo '-R coq Main' > _CoqProjectFull
	find coq -type f -name '*.v' >> _CoqProjectFull
	coq_makefile -f _CoqProjectFull -o Makefile.coq || \
	  (rm -f _CoqProjectFull Makefile.coq Makefile.coq.conf; exit 1)
	make -f Makefile.coq || \
	  (rm -f _CoqProjectFull Makefile.coq Makefile.coq.conf; exit 1)
	rm -f _CoqProjectFull Makefile.coq Makefile.coq.conf

lint: main
	./scripts/lint-general.rb $(shell \
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
	); \
	LINT_GENERAL_EXIT_CODE=$$?; \
	./scripts/lint-imports.rb '^\s*Require ' 'coqc -R coq Main ?' $(shell \
	  find . -type d \( \
	    -path ./.git \
	  \) -prune -o \( \
	    -name '*.v' \
	  \) -print \
	); \
	LINT_REQUIRES_EXIT_CODE=$$?; \
	./scripts/lint-imports.rb '^\s*Import ' 'coqc -R coq Main ?' $(shell \
	  find . -type d \( \
	    -path ./.git \
	  \) -prune -o \( \
	    -name '*.v' \
	  \) -print \
	); \
	LINT_IMPORTS_EXIT_CODE=$$?; \
	test "$$LINT_GENERAL_EXIT_CODE" -eq 0 && \
	test "$$LINT_REQUIRES_EXIT_CODE" -eq 0 && \
	test "$$LINT_IMPORTS_EXIT_CODE" -eq 0
	if grep --recursive --line-number --include '*.v' Admitted coq; then \
	  echo "Error: 'Admitted' found in proofs." 1>&2; \
	  exit 1; \
	fi

clean:
	rm -f _CoqProjectFull Makefile.coq \
	  $(shell \
	    find . -type d \( \
	      -path ./.git \
	    \) -prune -o \( \
	      -name '*.aux' -o \
	      -name '*.glob' -o \
	      -name '*.v.d' -o \
	      -name '*.vo' -o \
	      -name '*.vo.aux' -o \
	      -name 'Makefile.coq.conf' \
	    \) -print \
	  )

docker-deps:
	docker build -t stephanmisc/coq:8.8.0 scripts

docker-build:
	CONTAINER="$$( \
	  docker create --rm --user=root stephanmisc/coq:8.8.0 bash -c ' \
	    chown -R user:user repo && \
	    su user -s /bin/bash -l -c \
	      "cd repo && make clean && make main lint" \
	  ' \
	)" && \
	docker cp . "$$CONTAINER:/home/user/repo" && \
	docker start --attach "$$CONTAINER"
