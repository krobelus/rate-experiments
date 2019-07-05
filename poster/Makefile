all: INF_Poster.pdf INF_Poster_example.pdf

%.pdf: %.tex
	pdflatex $<

clean:
	rm -f *.aux *.log *.pdf *.nav *.snm *.toc *.out
