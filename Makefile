.PHONY: all submodules plugin cplugin install clean


all theories/Extraction/extraction.vo: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries -j`nproc`
	$(MAKE) -C theories -j`nproc`

theories/Makefile: theories/_CoqProject
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile: libraries/_CoqProject
	cd libraries;coq_makefile -f _CoqProject -o Makefile


submodules:
	git submodule update
	./make_submodules.sh


plugin: all plugin/CertiCoq.vo

plugin/Makefile: plugin/_CoqProject
	cd plugin ; coq_makefile -f _CoqProject -o Makefile

plugin/CertiCoq.vo: all plugin/Makefile theories/Extraction/extraction.vo
	bash ./make_plugin.sh plugin


cplugin: all cplugin/CertiCoq.vo

cplugin/Makefile: cplugin/_CoqProject
	cd cplugin ; coq_makefile -f _CoqProject -o Makefile

cplugin/CertiCoq.vo: all cplugin/Makefile theories/ExtractionVanilla/extraction.vo
	bash ./make_plugin.sh cplugin


install: plugin cplugin
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C plugin install
	$(MAKE) -C cplugin install


clean:
	$(MAKE) -C libraries clean
	$(MAKE) -C theories clean
	$(MAKE) -C plugin clean
	$(MAKE) -C cplugin clean
	rm -f `find theories -name "*.ml*"`
	rm -rf plugin/extraction
