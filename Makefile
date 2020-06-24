
all: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries
	$(MAKE) -C theories

plugin/CertiCoq.vo: plugin/Makefile theories/Extraction/extraction.vo all
	sh ./make_plugin.sh

install: all plugin/CertiCoq.vo
	$(MAKE) -C libraries install
	$(MAKE) -C theories install
	$(MAKE) -C plugin install

theories/Makefile:
	cd theories;coq_makefile -f _CoqProject -o Makefile

plugin/Makefile:
	cd plugin;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile:
	cd libraries;coq_makefile -f _CoqProject -o Makefile

# needs https://github.com/aa755/paramcoq/tree/v86FullNames installed
theories/common/TermAbs_parametricity.vo: theories/common/TermAbs_parametricity.v
	cd theories/common; coqc -R . Common TermAbs_parametricity.v

clean:
	$(MAKE) clean -C libraries
#	$(MAKE) clean -C libraries/SquiggleEq
	$(MAKE) clean -C theories

cleanCoqc:
	find -name *.vo | xargs rm
	find -name *.glob | xargs rm
	find -name *.v.d | xargs rm

gitsuperclean:
	git reset HEAD --hard
	git clean -xdf

submodules:
	git submodule update
	./make_submodules.sh

plugin: plugin/CertiCoq.vo

ci:
	git submodule update --init
	git submodule status
	sh make_submodules.sh
#	make all plugin
#	make install

.PHONY: submodules
