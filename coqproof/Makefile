.PHONY: all clean doc

export COQDOCFLAGS :=                                      \
  --toc --toc-depth 2 --html --interpolate         \
  --index indexpage --no-lib-name --parse-comments \
  --with-header doc/assets/header.html            \
  --with-footer doc/assets/footer.html


all:
	$(MAKE) -f Makefile.proj

clean:
	$(MAKE) -f Makefile.proj clean

doc:
	$(MAKE) -f Makefile.proj html
	rm -fr doc/html
	mv html doc/
	cp doc/assets/coqdoc.css doc/html
	cp doc/assets/coqdocjs.css doc/html
	cp doc/assets/coqdocjs.js doc/html
	cp doc/assets/config.js doc/html
	ln -s CoqDSC.Overview.html doc/html/index.html

Makefile.proj: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.proj
