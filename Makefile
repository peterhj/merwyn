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

.PHONY: all pre versions debug release test test-lang test-ir test-vm test-vmad

all: release

pre: versions

versions:
	$(Q)$(CARGO) --version > cargo.version
	$(Q)$(RUSTC) --version > rustc.version

debug: pre
	$(CARGO) build

release: pre
	$(CARGO) build --release

test: pre
	RUST_TEST_THREADS=1 $(CARGO) test --release -- --nocapture

test-lang: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test lang --release -- --nocapture

test-ir: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ir --release -- --nocapture

test-ir-debug: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ir -- --nocapture

test-ty: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test ty --release -- --nocapture

test-vm: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vm --release -- --nocapture

test-vmad: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vmad --release -- --nocapture

test-vmfix: pre
	RUST_TEST_THREADS=1 $(CARGO) test --test vmfix --release -- --nocapture
