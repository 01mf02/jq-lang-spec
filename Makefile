COMMON=defs.tex tour.md values.md syntax.md semantics.md impl.md
APPENDIX=appendix.tex json.md ujq.md
ICFP=icfp-intro.md $(COMMON) icfp-concl.md $(APPENDIX)
SPEC=spec-intro.md $(COMMON) $(APPENDIX)
DEPS=filter.lua literature.bib template.tex header.tex Makefile

PANOPTS= \
  --from=markdown+tex_math_single_backslash+tex_math_dollars+raw_tex \
  --lua-filter filter.lua \
  --bibliography=literature.bib \
  --standalone \
  --columns 10000 # TODO!

LATEXOPTS=$(PANOPTS) --natbib --template template.tex --include-in-header header.tex
HTMLOPTS=$(PANOPTS) --citeproc --mathjax


all: icfp.pdf spec.pdf spec.html
clean:
	rm *.aux *.bbl *.blg *.log *.pdf structure.tex icfp.tex spec.tex spec.html

icfp.tex: icfp.yaml $(ICFP) $(DEPS) structure.tex ccs.tex
	pandoc --metadata-file $< $(ICFP) $(LATEXOPTS) -o $@ -H ccs.tex

spec.tex: spec.yaml $(SPEC) $(DEPS)
	pandoc --metadata-file $< $(SPEC) $(LATEXOPTS) -o $@

spec.html: spec.yaml $(SPEC) $(DEPS)
	pandoc --metadata-file $< $(SPEC) $(HTMLOPTS) -o $@

%.pdf: %.tex
	xelatex $<
	bibtex $*
	xelatex $<
	xelatex $<

# remove trailing semicolons to suppress error messages
structure.tex: structure.dot
	dot2tex structure.dot --autosize --figonly | sed 's/0};/0}/' > $@
