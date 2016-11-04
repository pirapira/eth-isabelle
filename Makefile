.PHONY: all

all:
	isabelle build -d . all
document/output.pdf:
	sh document_generation.sh
