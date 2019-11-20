V ?= 0
ifeq ($(V),0)
  Q := @
else
  Q :=
endif

CARGO_FLAGS ?=
RUSTFLAGS ?= "-C target-cpu=native"

# TODO: Currently we are using some unstable features (plex requires some,
# while we also utilize 'non_ascii_idents'), so build with nightly.
#CARGO := cargo
#RUSTC := rustc
CARGO := RUSTFLAGS=$(RUSTFLAGS) cargo +nightly
RUSTC := RUSTFLAGS=$(RUSTFLAGS) rustc +nightly

.PHONY: all clean docs rfcs pre versions debuglib lib debugtools tools test test-lang test-ir2 test-mach test-rngs test-ty2

all: lib

clean:
	$(Q)$(CARGO) clean

docs:
	@make -C docs

rfcs:
	@make -C docs/rfcs

pre: versions

versions:
	$(Q)$(CARGO) --version > cargo.version
	$(Q)$(RUSTC) --version > rustc.version

debuglib: pre
	$(CARGO) build $(CARGO_FLAGS) --lib

lib: pre
	$(CARGO) build $(CARGO_FLAGS) --release --lib

debugtools: debuglib
	$(CARGO) build $(CARGO_FLAGS) --bins

tools: lib
	$(CARGO) build $(CARGO_FLAGS) --release --bins

test: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --release -- --nocapture

test-lang: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --test lang --release -- --nocapture

test-ir2: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --test ir2 --release -- --nocapture

test-mach: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --test mach --release -- --nocapture

test-rngs: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --test rngs --release -- --nocapture

test-ty2: lib
	RUST_TEST_THREADS=1 $(CARGO) test $(CARGO_FLAGS) --test ty2 --release -- --nocapture
