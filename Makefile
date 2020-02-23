.PHONY: verify clean

verify:
	rm -f \
          .Makefile.coq.d \
          .lia.cache \
          Makefile.coq \
          Makefile.coq.conf \
          _CoqProjectFull
	echo '-R proofs Main' > _CoqProjectFull
	find proofs -type f -name '*.v' >> _CoqProjectFull
	coq_makefile -f _CoqProjectFull -o Makefile.coq || (rm -f \
            .Makefile.coq.d \
            .lia.cache \
            Makefile.coq \
            Makefile.coq.conf \
            _CoqProjectFull; \
          exit 1)
	make -f Makefile.coq || (rm -f \
            .Makefile.coq.d \
            .lia.cache \
            Makefile.coq \
            Makefile.coq.conf \
            _CoqProjectFull; \
          exit 1)
	rm -f \
          .Makefile.coq.d \
          .lia.cache \
          Makefile.coq \
          Makefile.coq.conf \
          _CoqProjectFull

clean:
	rm -f \
          .Makefile.coq.d \
          .lia.cache \
          Makefile.coq \
          Makefile.coq.conf \
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
