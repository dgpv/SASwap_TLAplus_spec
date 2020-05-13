NAME = SASwap

all: check

check: build/metadir
	java -jar ${TLATOOLSDIR}/tla2tools.jar \
	    -config ${NAME}.cfg \
	    -workers 1 \
	    -metadir build/metadir \
	    -terse \
	    -cleanup \
	    -deadlock \
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
