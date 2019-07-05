all: INF_Poster.pdf INF_Poster_example.pdf

%.pdf: %.tex
	pdflatex -shell-escape -halt-on-error $<

clean:
	rm -f *.aux *.log *.pdf *.nav *.snm *.toc *.out
