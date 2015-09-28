SHELL:=/bin/bash

icreateMoveToLoc.hs : icreateMoveToLocExt.v
	cd ../.. ; scons src/examples/icreateMoveToLocExt.vo
	../shim/Haskell/postProcExt.sh $@
	echo "main = Ros.Node.runNode \"icreateSw\"  icreateRoshaskSwNode" >> $@

icreateMoveToLoc : icreateMoveToLoc.hs
	ghc $^ -main-is IcreateMoveToLoc -o  $@


clean:
	rm icreateMoveToLocExt.vo  *.hs *.o *.hi
