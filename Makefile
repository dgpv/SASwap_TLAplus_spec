NAME = SASwap_ZmnSCPxj

ifeq (${NUM_WORKERS},)
NUM_WORKERS = 1
endif

all: check

check: build/metadir
	java -jar ${TLATOOLSDIR}/tla2tools.jar \
	    -config ${NAME}.cfg \
	    -workers ${NUM_WORKERS} \
	    -metadir build/metadir \
	    -terse \
	    -cleanup \
	    MC.tla

pdf: build/metadir
	java -cp ${TLATOOLSDIR}/tla2tools.jar tla2tex.TLA \
	    -metadir build/metadir \
	    -latexOutputExt pdf \
	    -latexCommand pdflatex \
	    -ptSize 12 \
	    -shade \
	    ${NAME}.tla

clean:
	rm -rf build

build:
	mkdir -p build

build/metadir:
	mkdir -p build/metadir

.PHONY: all check pdf clean
