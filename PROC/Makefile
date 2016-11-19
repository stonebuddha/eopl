OBJS = syntax.cmo core.cmo main.cmo

.PHONY: proof clean

PROC.exe: $(OBJS)
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

proof: proof.vo

proof.vo: proof.v
	coqc $<

clean:
	rm -rf *.exe *.cmi *.cmo *.vo *.glob
