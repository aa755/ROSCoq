SHELL:=/bin/bash

icreateMoveToLoc.hs : icreateMoveToLocExt.v
	scons --site-dir ../site_scons/ icreateMoveToLocExt.vo
	../src/shim/Haskell/postProcExt.sh $@
	echo "main = Ros.Node.runNode \"icreateSw\"  icreateRoshaskSwNode" >> $@

icreateMoveToLoc : icreateMoveToLoc.hs
	ghc $^ -main-is IcreateMoveToLoc -o  $@


clean:
	rm icreateMoveToLocExt.vo  *.hs *.o *.hi
