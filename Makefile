targets = epistemic_models.vo
srcs = epistemic_models.v trans_closures.v
docdir = ./docs
vobjs = $(srcs:.v=.vo)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)

epistemic_models.vo: trans_closures.vo

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc --gallina --utf8 -d $(docdir) $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
