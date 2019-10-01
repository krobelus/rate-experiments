plots := p
tables := t

all: build-dependencies tools results.csv $(plots) $(tables) \
	 thesis.pdf vutinfth/submission.pdf poster/poster.pdf

error := "*** Error: please install"
citeproc := $(error) pandoc-citeproc
fignos := $(error) pandoc-fignos using pipenv install and activate the pipenv virtual environment
placetable := $(error) pandoc-placetable using stack install

build-dependencies:
	@which pandoc-citeproc   >/dev/null || ( echo $(citeproc)   && exit 1 )
	@which pandoc-fignos     >/dev/null || ( echo $(fignos)     && exit 1 )
	@which pandoc-placetable >/dev/null || ( echo $(placetable) && exit 1 )

# pandoc := pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable
pandoc := pandoc --filter pandoc-fignos

# thesis.markdown: thesis.md $(tables) $(plots) Makefile
# 	$(pandoc) $< -o $@ -t gfm
# 	sed -i '1i# $(TITLE)' $@
abstract: thesis.md
	awk '/Abstract:/{a=1;$$1=""}{if(a)print}/^$$/{if(a)exit}' $< > $@
vutinfth/submission.pdf: vutinfth/submission.tex thesis.md $(tables) $(plots) Makefile abstract
	awk 'BEGIN{p=1}/^\\maketitle$$/{p=0}/^1./{p=1}/\\printbibliography/{p=0}{if(p)print}' thesis.md | \
	perl -ne 's/(\[|^)\d+(\.\d+)* /\1/; print' | \
	$(pandoc) --from=markdown -o vutinfth/thesis-for-submission.tex
	cd vutinfth && ln -sf ../p . && ln -sf ../t .
	cd vutinfth && sh build-all.sh
thesis.pdf: thesis.tex $(tables) $(plots) Makefile
	xelatex thesis
	biber thesis
	xelatex thesis
thesis.tex: thesis.md $(tables) $(plots) Makefile references.bib
	@# $(pandoc) --biblatex --bibliography=references.bib --csl=ieee.csl $< -o $@ --standalone
	$(pandoc) $< -o $@ --standalone
thesis.html: thesis.md $(tables) $(plots) Makefile
	$(pandoc) $< -o $@

results.csv: results.json csv.sh
	./csv.sh < $< > $@

$(plots): results.csv plots.ipynb
	rm -rf $@
	mkdir $@
	jupyter nbconvert --execute plots.ipynb --stdout >/dev/null

plots.html: plots.ipynb
	jupyter nbconvert $<

$(tables): results.csv table.py
	rm -rf $@
	mkdir $@
	./table.py $@ < $<

poster/poster.pdf: poster/poster.tex $(plots)
	cd poster && pdflatex -shell-escape -halt-on-error poster.tex
	cd poster && pdflatex -shell-escape -halt-on-error poster.tex

tools:
	$(MAKE) -C $@

clean: poster/clean
	rm -rf $(plots) t _minted-*
	rm -f *.csv *.html *.pdf *.bbl *.tex *.blg *.fdb_latexmk *.fls *.toc
	rm -f vgcore.* massif.out.* auto
	
poster/clean:
	cd poster && rm -f *.aux *.log *.pdf *.nav *.snm *.toc *.out *.vrb

format:
	fd \.sh\$$ | parallel checkbashisms
	fd \.py\$$ | parallel autopep8 --in-place --aggressive --aggressive
