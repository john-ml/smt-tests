all:
	for FILE in *.smt; do echo ---------- $$FILE ----------; z3 $$FILE; done
