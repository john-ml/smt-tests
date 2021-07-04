all: z3 cvc4 cvc5 alt-ergo

clean:
	rm *.tmp

c4: cvc4
cvc4:
	cpp proofs.smt2 | grep -v '^#' > proofs.smt2.tmp && \
          cvc4 --lang smt --incremental proofs.smt2.tmp && rm proofs.smt2.tmp

c5: cvc5
cvc5:
	cpp -D cvc4_1_8 proofs.smt2 | grep -v '^#' > proofs.smt2.tmp && \
          cvc4-1.8 --lang smt --incremental proofs.smt2.tmp && rm proofs.smt2.tmp

ae: alt-ergo

alt-ergo:
	cpp -D alt_ergo proofs.smt2 | grep -v '^#' > proofs.smt2.tmp.smt2 && \
          alt-ergo proofs.smt2.tmp.smt2 2> /dev/null | grep . && rm proofs.smt2.tmp.smt2

alt-ergo-verbose:
	cpp -D alt_ergo proofs.smt2 | grep -v '^#' > proofs.smt2.tmp.smt2 && \
          alt-ergo proofs.smt2.tmp.smt2 | grep . && rm proofs.smt2.tmp.smt2

z3:
	cpp -D z3 proofs.smt2 | grep -v '^#' > proofs.smt2.tmp && \
          z3 proofs.smt2.tmp && rm proofs.smt2.tmp

every-file-z3:
	for FILE in *.smt2; do echo ---------- $$FILE ----------; \
          cpp -D z3 $$FILE | grep -v '^#' > $$FILE.tmp && \
          z3 $$FILE.tmp && rm $$FILE.tmp; done
