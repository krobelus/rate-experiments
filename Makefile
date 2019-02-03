org_files := index.org table-difference.org table-difference-accepted.org table-performance.org
html_files := $(patsubst %.org,%.html,$(org_files))
pdf_file := index.pdf
plots := p/plots
tables := t/tables

# build:
# 	asciidoc -a latexmath index.asciidoc
# 	pandoc index.html -o index.pdf
# 	qutebrowser :reload
# 	@# asciidoctor -a latexmath index.asciidoc

# pandoc index.md -o index.tex --bibliography references.bib --standalone

all: build-dependencies tools hash-solved-instances results.csv \
	 $(plots) \
	 $(tables) \
	 README.html README.pdf README.markdown


error := "*** Error: please install"
citeproc := $(error) pandoc-citeproc
fignos := $(error) pandoc-fignos using pipenv install
placetable := $(error) pandoc-placetable using stack install
include := $(error) pandoc-include using stack install

build-dependencies:
	@which pandoc-citeproc   || ( echo $(citeproc)   && exit 1 )
	@which pandoc-fignos     || ( echo $(fignos)     && exit 1 )
	@which pandoc-placetable || ( echo $(placetable) && exit 1 )
#	@which pandoc-include    || ( echo $(include)    && exit 1 )

# dependencies:
# - pipenv install
# - https://github.com/mb21/pandoc-placetable
pandoc := pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable

README.markdown: README.md $(tables) $(plots)
	$(pandoc) $< -o $@ -t gfm
README.html: README.md $(tables) $(plots)
	$(pandoc) $< -o $@
README.pdf: README.md $(tables) $(plots)
	$(pandoc) $< -o $@

# dist: all index.md
# 	mv index.md README.md
# 	git add README.md -f $(html_files) $(pdf_file) p/*.png t/*.csv
# 	git commit -am 'add index.html and index.pdf'

# results.json is checked in!
# results.json: instances.txt checkers.txt benchmarks/.set-of-solved-instances results.py
# 	./results.py > $@

clean:
	rm -rf p t _minted-*
	rm -f *.csv *.html *.pdf *.bbl *.tex *.blg *.fdb_latexmk *.fls *.toc
	rm -f vgcore.* massif.out.* auto
	rm -f *.md

export := HOME=`realpath tools` emacs --batch -l export.el

# %.md: %.org $(tables)
# 	$(export) $< -f org-pandoc-export-to-markdown -f sleep

# %.html: %.org $(tables)
# 	$(export) $< -f org-html-export-to-html -f sleep

# %.pdf: %.org $(tables) $(plots)
# 	$(export) $< -f org-latex-export-to-pdf -f sleep

results.csv: results.json csv.sh
	./csv.sh < $< > $@

$(plots): results.csv plot.py
	rm -rf p
	mkdir p
	./plot.py p < $<
	touch $(plots)

$(tables): results.csv table.py
	rm -rf t
	mkdir t
	./table.py t < $<
	touch $(tables)

tools:
	$(MAKE) -C $@

format:
	fd \.sh\$$ | parallel checkbashisms
	fd \.py\$$ | parallel autopep8 --in-place --aggressive --aggressive

.PHONY: hash-solved-instances
hash-solved-instances:
	@# ./hash-solved-instances.sh # check if there is new output

# first hash
benchmarks/.set-of-solved-instances:
	touch $@

