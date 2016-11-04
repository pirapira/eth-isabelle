.PHONY: all deed

all:
	isabelle build -d . all
deed: document/output.pdf
document/output.pdf:
	sh document_generation.sh
