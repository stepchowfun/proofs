.PHONY: verify clean

verify:
	rm -f \
          .CoqMakefile.d \
          CoqMakefile \
          CoqMakefile.conf \
          _CoqProjectFull
	echo '-Q proofs Main' > _CoqProjectFull
	find proofs -type f -name '*.v' >> _CoqProjectFull
	coq_makefile -f _CoqProjectFull -o CoqMakefile || (rm -f \
            .CoqMakefile.d \
            CoqMakefile \
            CoqMakefile.conf \
            _CoqProjectFull; \
          exit 1)
	make -f CoqMakefile || (rm -f \
            .CoqMakefile.d \
            CoqMakefile \
            CoqMakefile.conf \
            _CoqProjectFull; \
          exit 1)
	rm -f \
          .CoqMakefile.d \
          CoqMakefile \
          CoqMakefile.conf \
          _CoqProjectFull

clean:
	rm -f \
          .CoqMakefile.d \
          CoqMakefile \
          CoqMakefile.conf \
          _CoqProjectFull \
	  $(shell \
	    find . -type d \( \
	      -path ./.git \
	    \) -prune -o \( \
	      -name '*.aux' -o \
	      -name '*.glob' -o \
	      -name '*.vo' -o \
	      -name '*.vok' -o \
	      -name '*.vos' \
	    \) -print \
	  )
