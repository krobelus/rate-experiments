all: poster.pdf

%.pdf: %.tex ../p
	pdflatex -shell-escape -halt-on-error $<

clean:
	rm -f *.aux *.log *.pdf *.nav *.snm *.toc *.out *.vrb
