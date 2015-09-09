SHELL:=/bin/bash

coqEcho.hs: Echo.v ../ROSStringMsg.v
	cd ../../../../; scons src/shim/Haskell/examples/Echo.vo
	pwd
	mv ../../../../coqEcho.hs ./
	../postProcExt.sh coqEcho.hs
	echo "main = Ros.Node.runNode \"echo\"  echoNode" >> coqEcho.hs

echo : coqEcho.hs
	ghc coqEcho.hs -main-is CoqEcho -o echo


clean:
	rm Echo.vo coqEcho.hs ../../../../coqEcho.hs *.o	
