plots := p
tables := t

all: build-dependencies tools results.csv $(plots) $(tables) \
	 README.pdf README.markdown README.tex poster/poster.pdf

error := "*** Error: please install"
citeproc := $(error) pandoc-citeproc
fignos := $(error) pandoc-fignos using pipenv install and activate the pipenv virtual environment
placetable := $(error) pandoc-placetable using stack install

build-dependencies:
	@which pandoc-citeproc   >/dev/null || ( echo $(citeproc)   && exit 1 )
	@which pandoc-fignos     >/dev/null || ( echo $(fignos)     && exit 1 )
	@which pandoc-placetable >/dev/null || ( echo $(placetable) && exit 1 )

TITLE := DRAT Proofs without Non-Redundant Reason Clause Deletions
TITLE += // Complete and Fast DRAT Proof Checking

pandoc := pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable

# diff example
# latexdiff (git show 1290044b6ce1285ce64ab9ce11075d0c01b7fc51:README.md
# | pandoc --filter pandoc-fignos --filter pandoc-citepro c --filter \
# pandoc-placetable --to latex --standalone | psub) README.tex | pandoc --from \
# latex -o diff.pdf

README.pdf: README.md $(tables) $(plots) Makefile
	$(pandoc) $< -o $@
README.markdown: README.md $(tables) $(plots) Makefile
	$(pandoc) $< -o $@ -t gfm
	sed -i '1i# $(TITLE)' $@
README.tex: README.md $(tables) $(plots) Makefile
	$(pandoc) $< -o $@ --standalone
README.html: README.md $(tables) $(plots) Makefile
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
