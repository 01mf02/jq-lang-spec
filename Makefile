FILENAME=defs.tex icfp-intro.md tour.md syntax.md semantics.md icfp-concl.md
#FILENAME=defs.tex json.md

pdf:
	pandoc $(FILENAME) \
	--lua-filter filter.lua \
	--citeproc \
	--from=markdown+tex_math_single_backslash+tex_math_dollars+raw_tex \
	--to=latex \
	--bibliography=literature.bib \
	--natbib \
	--output=icfp.pdf \
	--pdf-engine=xelatex \
	--standalone \
	--template template.tex \
	--include-in-header header.tex \
	--columns 10000 # TODO!

html:
	pandoc $(FILENAME).md \
	--lua-filter filter.lua \
	--citeproc \
	--from=markdown+tex_math_single_backslash+tex_math_dollars+markdown_in_html_blocks \
	--to=html5 \
	--output=$(FILENAME).html \
	--mathjax \
	#--standalone
