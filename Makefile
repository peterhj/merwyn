V ?= 0
ifeq ($(V),0)
  Q := @
else
  Q :=
endif

CARGO_FLAGS ?=

#CARGO := cargo
#RUSTC := rustc
CARGO := cargo +nightly $(CARGO_FLAGS)
RUSTC := rustc +nightly

.PHONY: all clean pre versions debuglib lib debugtools tools test test-lang test-ir test-mach test-rngs test-ty test-ty2 test-vm test-vmad

all: lib

clean:
	$(Q)$(CARGO) clean

pre: versions

versions:
	$(Q)$(CARGO) --version > cargo.version
	$(Q)$(RUSTC) --version > rustc.version

debuglib: pre
	$(CARGO) build --lib

lib: pre
	$(CARGO) build --release --lib

debugtools: debuglib
	$(CARGO) build --bins

tools: lib
	$(CARGO) build --release --bins

test: pre
	RUST_TEST_THREADS=1 $(CARGO) test --release -- --nocapture

test-lang: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test lang --release -- --nocapture

test-ir: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ir --release -- --nocapture

test-ir-debug: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ir -- --nocapture

test-mach: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test mach --release -- --nocapture

test-rngs: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test rngs --release -- --nocapture

test-ty: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ty --release -- --nocapture

test-ty2: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ty2 --release -- --nocapture

test-vm: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vm --release -- --nocapture

test-vmad: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vmad --release -- --nocapture

test-vmfix: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vmfix --release -- --nocapture
