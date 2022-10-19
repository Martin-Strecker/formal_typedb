# Run with
# make isabellmk     for initial setup 
# make isabellbd     for translating Isabelle theories to Latex
# make               for compiling Latex files

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


main.pdf: *.tex $(STYFILES) $(BIBFILES)
	pdflatex main; bibtex main; pdflatex main; pdflatex main

isabellebd:
	isabelle build -D ../Formal; cp $(GEN_TEXFILES) .
isabellemk:
	isabelle mkroot ../FORMAL
