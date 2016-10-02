LET.exe: syntax.cmo main.cmo
	@echo Linking $@
	ocamlc -o $@ -I `camlp5 -where` gramlib.cma syntax.cmo main.cmo

syntax.cmo: syntax.cmi
main.cmo: syntax.cmi

%.cmi: %.mli
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

%.cmo: %.ml
	ocamlc -c -I `camlp5 -where` -pp 'camlp5o pa_extend.cmo' $<

clean::
	rm -rf LET.exe *.cmi *.cmo
