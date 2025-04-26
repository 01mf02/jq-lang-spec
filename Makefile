COMMON=tour.md syntax.md values.md semantics.md
ICFP=defs.tex icfp-intro.md $(COMMON) impl.md icfp-concl.md json.md
SPEC=defs.tex spec-intro.md $(COMMON) json.md
DEPS=filter.lua literature.bib template.tex header.tex Makefile

PANOPTS= \
  --from=markdown+tex_math_single_backslash+tex_math_dollars+raw_tex \
  --to=latex \
  --lua-filter filter.lua \
  --bibliography=literature.bib --natbib \
  --template template.tex \
  --include-in-header header.tex \
  --standalone \
  --columns 10000 # TODO!

all: icfp.pdf spec.pdf
clean:
	rm *.aux *.bbl *.blg *.log *.pdf structure.tex icfp.tex spec.tex

icfp.tex: $(DEPS) $(ICFP) structure.tex
	pandoc --metadata-file icfp.yaml $(ICFP) $(PANOPTS) -o $@

spec.tex: $(DEPS) $(SPEC)
	pandoc --metadata-file spec.yaml $(SPEC) $(PANOPTS) -o $@

%.pdf: %.tex
	xelatex $<
	bibtex $*
	xelatex $<
	xelatex $<

html:
	pandoc $(FILENAME).md \
	--lua-filter filter.lua \
	--citeproc \
	--from=markdown+tex_math_single_backslash+tex_math_dollars+markdown_in_html_blocks \
	--to=html5 \
	--output=$(FILENAME).html \
	--mathjax \
	#--standalone

# remove trailing semicolons to suppress error messages
structure.tex: structure.dot
	dot2tex structure.dot --autosize --figonly | sed 's/0};/0}/' > $@
