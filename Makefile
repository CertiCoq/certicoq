.PHONY: all submodules plugin install clean


all: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries
	$(MAKE) -C theories

theories/Makefile:
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile:
	cd libraries;coq_makefile -f _CoqProject -o Makefile


submodules:
	git submodule update
	./make_submodules.sh


plugin: plugin/CertiCoq.vo

plugin/Makefile:
	cd plugin ; coq_makefile -f _CoqProject -o Makefile

plugin/CertiCoq.vo: all plugin/Makefile theories/Extraction/extraction.vo
	sh ./make_plugin.sh


install: all plugin/CertiCoq.vo
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C plugin install


clean:
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
