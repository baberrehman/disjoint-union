
## Name of the submakefile generated by coq_makefile
COQMKFILENAME=CoqSrc.mk

LIBNAME="Top"

SYNTAX=syntax
TARGET=rules

FILES    = syntax
VFILES   = $(foreach i, $(FILES), $(i).v)

.SECONDARY: $(VFILES)

all: coq

quick:  $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk quick

coq: $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk

%.vo: %.v
	@$(MAKE) -f CoqSrc.mk $*.vo

$(COQMKFILENAME): Makefile
	{ echo "-R . $(LIBNAME)" ; ls *.v ; } > _CoqProject && coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o $(COQMKFILENAME)


coqclean:
	rm -f .*.d *.conf .*.aux *.v-e *.v.d *.vo *.vos *.vok *.glob $(COQMKFILENAME) *_CoqProject

clean: coqclean
