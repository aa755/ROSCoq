#designed to be run in ROSCoq/examples/someExample/coqdoc
for f in *.html
do 
	cat ../../../doc/noCacheHeader.html > temp
	tail -n +5 $f >> temp
	mv temp  $f
done
