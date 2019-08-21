TOOLS := tmux runlim parallel zstd gratgen drat-trim to-clrat rate sick-check drat2cdrat sysstat

all: bin $(TOOLS) acl2-devel .emacs.d

bin:
	mkdir -p bin

libevent:
	git clone -b release-2.1.8-stable https://github.com/libevent/libevent
	cd libevent && ./autogen.sh && ./configure && make

tmux: libevent
	curl -L https://github.com/tmux/tmux/releases/download/2.8/tmux-2.8.tar.gz -o tmux-2.8.tar.gz
	tar xf tmux-2.8.tar.gz
	ln -s tmux-2.8 tmux
	cd tmux && \
	   LIBEVENT_LIBS='-levent -L../libevent/.libs' \
	   LIBEVENT_CFLAGS='-I../libevent/include' \
	   ./configure
	cd tmux && make
	cd bin && ln -s ../tmux/tmux .

runlim:
	tar xf runlim-1.12.tar.gz
	ln -s runlim-1.12 runlim
	cd runlim && ./configure.sh && make
	cd bin && ln -s ../runlim/runlim .

parallel:
	wget https://ftpmirror.gnu.org/parallel/parallel-20190122.tar.bz2
	bzip2 -dc parallel-20190122.tar.bz2 | tar xvf -
	ln -s parallel-20190122 parallel
	cd parallel && ./configure && make
	cd bin && ln -s ../parallel/src/parallel .
	echo will cite | bin/parallel --citation

zstd:
	git clone -b v1.3.8 https://github.com/facebook/zstd
	cd zstd && make
	cd bin && ln -s ../zstd/zstd .

gratgen:
	curl -O http://www21.in.tum.de/~lammich/grat/gratgen.tgz
	tar xf gratgen.tgz
	mkdir -p gratgen/build
	cd gratgen/build && cmake .. && make
	cd bin && ln -s ../gratgen/build/gratgen .

drat-trim:
	git clone https://github.com/marijnheule/drat-trim
	git -C drat-trim checkout 59d345a04ec0fe1694e2fef87ef7698a826683d8
	make -C drat-trim
	cd bin && ln -s ../drat-trim/drat-trim .

to-clrat: drat-trim
	cd drat-trim && gcc -o $@ to-clrat.c
	cd bin && ln -s ../drat-trim/to-clrat .

rust:
	which cargo >/dev/null 2>/dev/null || ./install-rust.sh
	mkdir -p rust

rate: rust # TODO ?!
	test -d rate || git clone -b master https://github.com/krobelus/rate
	cd rate && git config receive.denyCurrentBranch updateInstead
	cd rate && cargo build --release
	cd bin && ln -sf ../rate/target/release/rate .

sick-check: rate
	cd bin && ln -sf ../rate/target/release/sick-check .

drat2cdrat: rate
	cd bin && ln -sf ../rate/target/release/drat2cdrat .

sbcl:
	curl -O https://netcologne.dl.sourceforge.net/project/sbcl/sbcl/1.4.16/sbcl-1.4.16-x86-64-linux-binary.tar.bz2
	tar xf sbcl-1.4.16-x86-64-linux-binary.tar.bz2
	ln -s sbcl-1.4.16-x86-64-linux sbcl

acl2-devel: sbcl
	git clone -b 8.1 https://github.com/acl2-devel/acl2-devel
	cd acl2-devel && make LISP="$$(realpath ../sbcl/run-sbcl.sh)"
	./build-lrat-check.sh

.emacs.d:
	-HOME=`realpath .` emacs -l elisp-packages.el --batch --kill
	mkdir -p $@
	@echo emacs is only needed for document generation

sysstat:
	curl -OL http://pagesperso-orange.fr/sebastien.godard/sysstat-12.1.3.tar.xz
	test 4601f9eee08379d77a0774371b66ed54151118c8 = "$$(sha1sum sysstat-12.1.3.tar.xz | awk '{print $$1}')"
	tar xf sysstat-12.1.3.tar.xz
	ln -s sysstat-12.1.3 sysstat
	cd sysstat && ./configure && make
	cd bin && ln -s ../sysstat/iostat .
