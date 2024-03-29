BASEDIR=../..


default: compile run

PLUGINS=plugin.so plugin2.so sub/plugin.so sub/plugin3.so plugin4.so mypack.so packed1.so packed1_client.so pack_client.so plugin_ref.so plugin_high_arity.so plugin_ext.so plugin_simple.so bug.so plugin_thread.so plugin4_unix.so a.so b.so c.so

ADD_COMPFLAGS=-thread

compile: $(PLUGINS) main mylib.so

run:
	@printf " ... testing 'main'"
	@./main plugin_thread.so > result
	@diff -q reference result > /dev/null || (echo " => failed" && exit 1)
	@echo " => passed"

main: api.cmx main.cmx
	@$(OCAMLOPT) -thread -o main -linkall unix.cmxa threads.cmxa dynlink.cmxa api.cmx main.cmx $(PTHREAD_LINK)

main_ext: api.cmx main.cmx factorial.$(O)
	@$(OCAMLOPT) -o main_ext dynlink.cmxa api.cmx main.cmx factorial.$(O)

sub/plugin3.cmx: sub/api.cmi sub/api.cmx sub/plugin3.ml
	@(cd sub; mv api.cmx api.cmx.bak; $(OCAMLOPT) -c $(COMPFLAGS) plugin3.ml; mv api.cmx.bak api.cmx)

plugin2.cmx: api.cmx plugin.cmi plugin.cmx
	@(mv plugin.cmx plugin.cmx.bak; $(OCAMLOPT) -c $(COMPFLAGS) plugin2.ml; mv plugin.cmx.bak plugin.cmx)

sub/api.so: sub/api.cmi sub/api.ml
	@(cd sub; $(OCAMLOPT) -c $(COMPFLAGS) $(SHARED) api.ml)

sub/api.cmi: sub/api.mli
	@(cd sub; $(OCAMLOPT) -c $(COMPFLAGS) api.mli)

sub/api.cmx: sub/api.cmi sub/api.ml
	@(cd sub; $(OCAMLOPT) -c $(COMPFLAGS) api.ml)

plugin.cmx: api.cmx plugin.cmi
sub/plugin.cmx: api.cmx
plugin4.cmx: api.cmx
main.cmx: api.cmx
plugin_ext.cmx: api.cmx plugin_ext.ml
	@$(OCAMLOPT) -c $(COMPFLAGS) plugin_ext.ml

plugin_ext.so: factorial.$(O) plugin_ext.cmx
	@$(OCAMLOPT) $(COMPFLAGS) -shared -o plugin_ext.so factorial.$(O) plugin_ext.cmx

plugin4_unix.so: plugin4.cmx
	@$(OCAMLOPT) -shared -o plugin4_unix.so unix.cmxa plugin4.cmx

packed1_client.cmx: packed1.cmx

pack_client.cmx: mypack.cmx

packed1.cmx: api.cmx packed1.ml
	@$(OCAMLOPT) -c $(COMPFLAGS) -for-pack Mypack packed1.ml

mypack.cmx: packed1.cmx
	@$(OCAMLOPT) $(COMPFLAGS) -S -pack -o mypack.cmx packed1.cmx

mylib.cmxa: plugin.cmx plugin2.cmx
	@$(OCAMLOPT) $(COMPFLAGS) -a -o mylib.cmxa plugin.cmx plugin2.cmx

factorial.$(O): factorial.c
	@$(OCAMLOPT) -c -ccopt "$(SHAREDCCCOMPOPTS)" factorial.c

promote:
	@cp result reference

clean: defaultclean
	@rm -f result *.so *.o *.cm* main main_ext *.exe *.s *.asm *.obj
	@rm -f *.a *.lib
	@rm -f sub/*.so sub/*.o sub/*.cm* sub/*.s sub/*.asm sub/*.obj

include $(BASEDIR)/makefiles/Makefile.common
