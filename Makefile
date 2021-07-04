all: z3 cvc4 cvc5

clean:
	rm *.tmp

cvc4:
	cpp skolem.smt | grep -v '^#' > skolem.smt.tmp && \
          cvc4 --lang smt --incremental skolem.smt.tmp && rm skolem.smt.tmp

cvc5:
	cpp -D cvc4_1_8 skolem.smt | grep -v '^#' > skolem.smt.tmp && \
          cvc4-1.8 --lang smt --incremental skolem.smt.tmp && rm skolem.smt.tmp

z3:
	cpp -D z3 skolem.smt | grep -v '^#' > skolem.smt.tmp && \
          z3 skolem.smt.tmp && rm skolem.smt.tmp

every-file-z3:
	for FILE in *.smt; do echo ---------- $$FILE ----------; \
          cpp -D z3 $$FILE | grep -v '^#' > $$FILE.tmp && \
          z3 $$FILE.tmp && rm $$FILE.tmp; done

every-file-cvc4:
	for FILE in *.smt; do echo ---------- $$FILE ----------; \
          cpp $$FILE | grep -v '^#' > $$FILE.tmp && \
          cvc4 --lang smt --incremental $$FILE.tmp && \
          rm $$FILE.tmp; done
