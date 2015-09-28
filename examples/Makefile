SHELL:=/bin/bash

icreateMoveToLoc.hs : icreateMoveToLocExt.v
	scons src/examples/icreateMoveToLocExt.vo
	../src/shim/Haskell/postProcExt.sh $@
	echo "main = Ros.Node.runNode \"icreateSw\"  icreateRoshaskSwNode" >> $@

icreateMoveToLoc : icreateMoveToLoc.hs
	ghc $^ -main-is IcreateMoveToLoc -o  $@


clean:
	rm icreateMoveToLocExt.vo  *.hs *.o *.hi
