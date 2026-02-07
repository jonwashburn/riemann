PDFLATEX ?= pdflatex
LATEXFLAGS ?= -interaction=nonstopmode

PAPER1 = paper1_farfield
PAPER2 = paper2_energy_barrier
PAPER3 = paper3_cutoff_conditional

.PHONY: all paper1 paper2 paper3 clean

all: paper1 paper2 paper3

paper1:
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER1).tex
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER1).tex

paper2:
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER2).tex
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER2).tex

paper3:
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER3).tex
	$(PDFLATEX) $(LATEXFLAGS) $(PAPER3).tex

clean:
	rm -f *.aux *.log *.out *.toc

