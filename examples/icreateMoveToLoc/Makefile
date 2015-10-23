SHELL:=/bin/bash

icreateMoveToLoc.hs : icreateMoveToLocExt.v
	scons --site-dir ../site_scons/ icreateMoveToLocExt.vo
	../src/shim/Haskell/postProcExt.sh $@
	echo "main = Ros.Node.runNode \"icreateSw\"  icreateRoshaskSwNode" >> $@
	echo "IMPORTANT!! : open icreateMoveToLoc.hs and in the type of qplus_strext0, change Prelude.Either () () to  Prelude.Either Any Any. Only then will it compile."

icreateMoveToLoc : icreateMoveToLoc.hs
	ghc $^ -main-is IcreateMoveToLoc -o  $@


clean:
	rm icreateMoveToLocExt.vo  *.hs *.o *.hi
