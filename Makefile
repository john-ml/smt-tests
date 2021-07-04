all:
	z3 skolem.smt
	cvc4 --lang smt --incremental skolem.smt

every-file-z3:
	for FILE in *.smt; do echo ---------- $$FILE ----------; z3 $$FILE; done

every-file-cvc4:
	for FILE in *.smt; do echo ---------- $$FILE ----------; cvc4 --lang smt --incremental $$FILE; done
