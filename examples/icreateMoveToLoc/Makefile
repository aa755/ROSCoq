SHELL:=/bin/bash

icreateMoveToLoc.hs : haskellExtraction.v
	scons --site-dir ../../site_scons/ haskellExtraction.vo
	../../src/shim/Haskell/postProcExt.sh $@
	echo "main = Ros.Node.runNode \"icreateSw\"  icreateRoshaskSwNode" >> $@
	echo "IMPORTANT!! : open icreateMoveToLoc.hs and in the type of qplus_strext0, change Prelude.Either () () to  Prelude.Either Any Any. Only then will it compile."

icreateMoveToLoc : icreateMoveToLoc.hs
	ghc $^ -main-is IcreateMoveToLoc -o  $@

proof:
	scons --site-dir ../../site_scons/ correctness.vo

coqdoc:
	scons --site-dir ../../site_scons/ -j4 -k
	rm -rf coqdoc
	cp SConstruct SConstruct.backup
	cat SConstruct.coqdoc >> SConstruct
	scons --site-dir ../../site_scons/ coqdoc
	cp SConstruct.backup SConstruct
	cp msgSeqDiagram.svg coqdoc/
	cd coqdoc; ../../../scripts/patchNoCache.sh

coqdocweb:
	rm -rf ~/homepage/MyWeb/ROSCoq/coqdocnew/
	cp -r coqdoc ~/homepage/MyWeb/ROSCoq/coqdocnew
	
	
clean:
	rm icreateMoveToLocExt.vo  *.hs *.o *.hi
