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
	for FILE in $(shell \
	  find . -type d \( \
	    -path ./.git \
	  \) -prune -o \( \
	    -name '*.v' \
	  \) -print \
	); do \
	  echo "Checking for unused or unsorted imports: $$FILE"; \
	  TEMP_IMPORTS_FILE="$$(mktemp)"; \
	  grep 'Require' "$$FILE" > "$$TEMP_IMPORTS_FILE"; \
	  if ! sort --check "$$TEMP_IMPORTS_FILE" > /dev/null 2>&1; then \
	    echo "Unsorted imports in $$FILE:" 1>&2; \
	    echo 1>&2; \
	    cat "$$TEMP_IMPORTS_FILE" 1>&2; \
	    rm "$$TEMP_IMPORTS_FILE"; \
	    exit 1; \
	  fi; \
	  while read -r LINE; do \
	    TEMP_COQ_FILE="$${FILE%.*}Temp.v"; \
	    grep -v -x "$$LINE" "$$FILE" > "$$TEMP_COQ_FILE"; \
	    if coqc -R coq Main "$$TEMP_COQ_FILE" > /dev/null 2>&1; then \
	      echo "Unused import in $$FILE:" 1>&2; \
	      echo "  $$LINE" 1>&2; \
	      rm "$$TEMP_COQ_FILE"; \
	      rm "$$TEMP_IMPORTS_FILE"; \
	      exit 1; \
	    fi; \
	    rm "$$TEMP_COQ_FILE"; \
	  done < "$$TEMP_IMPORTS_FILE"; \
	  rm "$$TEMP_IMPORTS_FILE"; \
	done

clean:
	rm -f _CoqProjectFull Makefile.coq \
	  $(shell \
	    find . -type d \( \
	      -path ./.git \
	    \) -prune -o \( \
	      -name '*.aux' -o \
	      -name '*.glob' -o \
	      -name '*.v.d' -o \
	      -name '*.tmp.v' -o \
	      -name '*.vo' -o \
	      -name '*.vo.aux' -o \
	      -name 'Makefile.coq.conf' \
	    \) -print \
	  )

docker-deps:
	docker build -t stephanmisc/coq:8.7.2 scripts

docker-build:
	CONTAINER="$$( \
	  docker create --rm --user=root stephanmisc/coq:8.7.2 bash -c ' \
	    chown -R user:user repo && \
	    su user -s /bin/bash -l -c \
	      "cd repo && make clean && make main lint" \
	  ' \
	)" && \
	docker cp . "$$CONTAINER:/home/user/repo" && \
	docker start --attach "$$CONTAINER"
