GEN_DIR = ../Formal/output/document/
GEN_TEXFILES = $(GEN_DIR)/Syntax.tex
STABLE_TEXFILES = main.tex

STYFILES = comment.sty \
	isabelle.sty \
	isabellesym.sty \
	isabelletags.sty \
	pdfsetup.sty \
	railsetup.sty

BIBFILES = main.bib

all: main.pdf
	isabelle build -D ../Formal; cp $(GEN_TEXFILES) .

main.pdf: *.tex $(STYFILES) $(BIBFILES)
	pdflatex main; bibtex main; pdflatex main; pdflatex main

isabellemk:
	isabelle mkroot ../FORMAL
