src := markdown
# dst := slidy
pdfdst := beamer

slides.pdf: slides.md Makefile
	pandoc -f $(src) -t $(pdfdst) -s $< -o $@

all: slides.pdf slides.html
	
htmldst := revealjs -V revealjs-url=https://revealjs.com

slides.html: slides.md Makefile
	pandoc -f $(src) -t $(htmldst) -s $< -o $@
	qutebrowser :reload >/dev/null 2>&1 ||:
