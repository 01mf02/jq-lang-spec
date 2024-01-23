all: main.html

clean:
	rm operators.html main.html

MATHJAX=https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js

operators.html: operators.sty
	(echo '<div style="display:none">$$$$' && \
	 cat $< && \
	 echo '$$$$</div>') > $@

%.pdf: %.md header.tex operators.sty
	pandoc -H header.tex $< -s -o $@

%.html: %.md operators.html
	pandoc -H operators.html --mathjax=$(MATHJAX) $< -s -o $@
