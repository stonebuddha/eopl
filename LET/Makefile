OBJS = syntax.cmo core.cmo main.cmo

LET.exe: $(OBJS)
	@echo Linking $@
	ocamlc -o $@ -I `camlp5 -where` gramlib.cma $(OBJS)

syntax.cmi:
syntax.cmo: syntax.cmi
core.cmi: syntax.cmi
core.cmo: syntax.cmi core.cmi
main.cmo: syntax.cmi core.cmi

%.cmi: %.mli
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

%.cmo: %.ml
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

proof: proof.v
	coqc -R ../common Common $<

clean::
	rm -rf *.exe *.cmi *.cmo *.vo *.glob
