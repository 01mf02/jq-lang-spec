# keep intermediate files
.SECONDARY:

HF=hyperfine -M 10 --export-json $@ -L jq $(JAQ),$(JQ),$(GOJQ)

JQ=jq
JAQ=jaq
GOJQ=gojq
HEADER="f	time-jaq	time-jq	time-gojq"

upd: upd-arr.tsv upd-obj.tsv
interpreters.tsv: bf-fib.json wsjq-hopper.json jqjq-implode.json jqjq-test.json
	(echo $(HEADER) && cat $^ | $(JQ) -srf interpreters.jq) > $@

bf-fib.json:
	$(HF) "{jq} -sRrf bf.jq -R fib.bf"

wsjq-hopper.json: wsjq/wsjq pik4ez-ascii/hopper.ws 
	$(HF) "$< --jq={jq} --no-underflow pik4ez-ascii/hopper.ws"

jqjq-implode.json: jqjq/jqjq
	$(HF) "JQ={jq} $< -n 'def f: 1,8; [f,f] | map(.+105) | implode'"

jqjq-test.json: jqjq
	$(HF) "make -C $< JQ={jq} test-jqjq"

# does not work ATM: https://github.com/wader/jqjq/issues/41
jqjq-bf-fib.json: jqjq/jqjq
	$(HF) 'JQ={jq} $< -n "\"$$(cat fib.bf)\" | $$(cat bf.jq)"'

upd-arr.json:
	$(HF) -L f '.','[.[] | .]','.[] |= .','getpath(path(.[])) |= .' '{jq} -n "[range(1000000)] | {f} | empty"'

upd-obj.json:
	$(HF) -L f '.','{a: .a | [.[] | .]}','.a[] |= .','getpath(path(.a[])) |= .' '{jq} -n "{a: [range(1000000)]} | {f} | empty"'

upd-%.tsv: upd-%.json
	(echo $(HEADER) && $(JQ) -r -f upd.jq $<) > $@
