OBJS = support.cmo syntax.cmo translator.cmo core.cmo main.cmo

.PHONY: clean

LEXICAL-EXT.exe: $(OBJS)
	@echo Linking $@
	ocamlc -o $@ -I `camlp5 -where` gramlib.cma $(OBJS)

support.cmi:
support.cmo: support.cmi
syntax.cmi:
syntax.cmo: syntax.cmi
translator.cmi: syntax.cmi
translator.cmo : syntax.cmi translator.cmi
core.cmi: syntax.cmi
core.cmo: support.cmi syntax.cmi core.cmi
main.cmo: syntax.cmi translator.cmi core.cmi

%.cmi: %.mli
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

%.cmo: %.ml
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

clean:
	rm -rf *.exe *.cmi *.cmo
