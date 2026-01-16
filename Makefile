.PHONY: verify clean

verify:
	rm -f \
          .RocqMakefile.d \
          .lia.cache \
          RocqMakefile \
          RocqMakefile.conf \
          _RocqProjectFull
	cp _RocqProject _RocqProjectFull
	find proofs_rocq -type f -name '*.v' >> _RocqProjectFull
	rocq makefile -f _RocqProjectFull -o RocqMakefile || (rm -f \
            .RocqMakefile.d \
            .lia.cache \
            RocqMakefile \
            RocqMakefile.conf \
            _RocqProjectFull; \
          exit 1)
	make -f RocqMakefile || (rm -f \
            .RocqMakefile.d \
            .lia.cache \
            RocqMakefile \
            RocqMakefile.conf \
            _RocqProjectFull; \
          exit 1)
	rm -f \
          .RocqMakefile.d \
          .lia.cache \
          RocqMakefile \
          RocqMakefile.conf \
          _RocqProjectFull

clean:
	rm -f \
          .RocqMakefile.d \
          .lia.cache \
          RocqMakefile \
          RocqMakefile.conf \
          _RocqProjectFull \
	  $(shell \
	    find . -type d \( \
	      -path ./.git -o \
	      -path ./.lake \
	    \) -prune -o \( \
	      -name '*.aux' -o \
	      -name '*.glob' -o \
	      -name '*.vo' -o \
	      -name '*.vok' -o \
	      -name '*.vos' \
	    \) -print \
	  )
