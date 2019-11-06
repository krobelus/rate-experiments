format := revealjs -V revealjs-url=https://revealjs.com
slides.html: slides.md Makefile
	pandoc -t $(format) -s $< -o $@
	qutebrowser :reload >/dev/null 2>&1 ||:
