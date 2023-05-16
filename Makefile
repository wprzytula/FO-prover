.PHONY: all

all: FO-prover

FO-prover: FORCE
	cargo build --release && cp target/release/prover FO-prover

debug: FORCE
	cargo build && cp target/debug/prover FO-prover

FORCE: ;

FO-prover-hs: FO-prover.hs *.hs
	ghc -o FO-prover FO-prover.hs

clean:
	rm -f FO-prover *.hi *.o && cargo clean
