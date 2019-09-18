plots := p
tables := t

all: build-dependencies tools results.csv $(plots) $(tables) \
	 thesis.pdf thesis.tex poster/poster.pdf

error := "*** Error: please install"
citeproc := $(error) pandoc-citeproc
fignos := $(error) pandoc-fignos using pipenv install and activate the pipenv virtual environment
placetable := $(error) pandoc-placetable using stack install

build-dependencies:
	@which pandoc-citeproc   >/dev/null || ( echo $(citeproc)   && exit 1 )
	@which pandoc-fignos     >/dev/null || ( echo $(fignos)     && exit 1 )
	@which pandoc-placetable >/dev/null || ( echo $(placetable) && exit 1 )

pandoc := pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable

thesis.pdf: thesis.md $(tables) $(plots) Makefile
	$(pandoc) $< -o $@
# thesis.markdown: thesis.md $(tables) $(plots) Makefile
# 	$(pandoc) $< -o $@ -t gfm
# 	sed -i '1i# $(TITLE)' $@
thesis.tex: thesis.md $(tables) $(plots) Makefile
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
