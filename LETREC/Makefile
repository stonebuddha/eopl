OBJS = support.cmo syntax.cmo core.cmo main.cmo

LETREC.exe: $(OBJS)
	@echo Linking $@
	ocamlc -o $@ -I `camlp5 -where` gramlib.cma $(OBJS)

support.cmi:
support.cmo: support.cmi
syntax.cmi:
syntax.cmo: syntax.cmi
core.cmi: syntax.cmi
core.cmo: support.cmi syntax.cmi core.cmi
main.cmo: syntax.cmi core.cmi

%.cmi: %.mli
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

%.cmo: %.ml
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

proof: proof.v
	coqc $<

clean::
	rm -rf *.exe *.cmi *.cmo *.vo *.glob
