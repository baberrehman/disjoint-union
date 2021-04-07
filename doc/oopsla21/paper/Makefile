OTT_OPTS  = -tex_show_meta false
OTT_FILES  = ../spec/rules.ott

MAIN = paper

RULESFILE = ott-rules.tex

AUTOGEN = sections/introduction.mng sections/overview.mng sections/union.mng sections/intersection.mng sections/discussion.mng \
          sections/related.mng sections/conclusion.mng

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(wildcard sections/*.tex) paper.bib $(AUTOGEN)
	@latexmk -pdf $(@:.pdf=.tex)

$(RULESFILE): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

%.mng: %.tex $(RULESFILE)
	ott -tex_wrap false $(OTT_OPTS) -tex_filter $*.tex $*.mng $(OTT_FILES)

clean:
	@latexmk -c
	@rm -f $(MAIN).pdf $(RULESFILE)  *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg bundle.tar.gz sections/*.mng *.bbl

.PHONY: all clean
