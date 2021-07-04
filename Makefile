all: z3 cvc4 cvc5

clean:
	rm *.tmp

cvc4:
	cpp skolem.smt2 | grep -v '^#' > skolem.smt2.tmp && \
          cvc4 --lang smt --incremental skolem.smt2.tmp && rm skolem.smt2.tmp

cvc5:
	cpp -D cvc4_1_8 skolem.smt2 | grep -v '^#' > skolem.smt2.tmp && \
          cvc4-1.8 --lang smt --incremental skolem.smt2.tmp && rm skolem.smt2.tmp

z3:
	cpp -D z3 skolem.smt2 | grep -v '^#' > skolem.smt2.tmp && \
          z3 skolem.smt2.tmp && rm skolem.smt2.tmp

every-file-z3:
	for FILE in *.smt2; do echo ---------- $$FILE ----------; \
          cpp -D z3 $$FILE | grep -v '^#' > $$FILE.tmp && \
          z3 $$FILE.tmp && rm $$FILE.tmp; done
