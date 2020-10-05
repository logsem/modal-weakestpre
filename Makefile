all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	+make -f Makefile.coq $@

# Install build-dependencies
build-dep/opam: modal-weakestpre.opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <modal-weakestpre.opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Pinning build-dep package." && \
	  if opam --version | grep "^1\." -q; then \
	    BUILD_DEP_PACKAGE="$$(egrep "^name:" build-dep/opam | sed 's/^name: *"\(.*\)" */\1/')" && \
	    opam pin add -k path $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE".dev build-dep && \
	    opam reinstall --verbose $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE"; \
	  else \
	    opam install --verbose $(OPAMFLAGS) build-dep/; \
	  fi

docker-build-deps:
	docker build \
		--build-arg=NJOBS=4 \
		--tag simongregersen/modal-weakestpre:latest \
		--file Dockerfile.deps .

docker-push-deps:
	docker push simongregersen/modal-weakestpre:latest

docker-build:
	docker build \
	  --build-arg=NJOBS=4 \
          --pull \
	  --tag modal-weakestpre-compile:latest \
          --file Dockerfile . 

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
modal-weakestpre.opam: ;

.PHONY: all clean phony
