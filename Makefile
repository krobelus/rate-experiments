org_files := index.org table-difference.org table-difference-accepted.org table-performance.org
html_files := $(patsubst %.org,%.html,$(org_files))
plots := p/plots
tables := t/tables

all: build-dependencies tools hash-solved-instances results.csv \
	 $(plots) \
	 $(tables) \
	 README.pdf README.markdown poster


error := "*** Error: please install"
citeproc := $(error) pandoc-citeproc
fignos := $(error) pandoc-fignos using pipenv install
placetable := $(error) pandoc-placetable using stack install

build-dependencies:
	@which pandoc-citeproc   >/dev/null || ( echo $(citeproc)   && exit 1 )
	@which pandoc-fignos     >/dev/null || ( echo $(fignos)     && exit 1 )
	@which pandoc-placetable >/dev/null || ( echo $(placetable) && exit 1 )

# dependencies:
# - pipenv install
# - https://github.com/mb21/pandoc-placetable
pandoc := pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable

README.markdown: README.md $(tables) $(plots)
	$(pandoc) $< -o $@ -t gfm
	sed -i '1i# Complete and Competitive DRAT Checking' $@
README.html: README.md $(tables) $(plots)
	$(pandoc) $< -o $@
README.pdf: README.md $(tables) $(plots)
	$(pandoc) $< -o $@
README.tex: README.md $(tables) $(plots)
	$(pandoc) $< -o $@

results.csv: results.json csv.sh
	./csv.sh < $< > $@

$(plots): results.csv plots.ipynb
	rm -rf p
	mkdir p
	jupyter nbconvert --execute plots.ipynb --stdout >/dev/null
	touch $@

plots.html: plots.ipynb
	jupyter nbconvert $<

$(tables): results.csv table.py
	rm -rf t
	mkdir t
	./table.py t < $<
	touch $@

poster:
	$(MAKE) -C $@

tools:
	$(MAKE) -C $@

clean:
	rm -rf p t _minted-*
	rm -f *.csv *.html *.pdf *.bbl *.tex *.blg *.fdb_latexmk *.fls *.toc
	rm -f vgcore.* massif.out.* auto

format:
	fd \.sh\$$ | parallel checkbashisms
	fd \.py\$$ | parallel autopep8 --in-place --aggressive --aggressive

.PHONY: hash-solved-instances tools poster
hash-solved-instances:
	@# ./hash-solved-instances.sh # check if there is new output

# first hash
benchmarks/.set-of-solved-instances:
	touch $@

	