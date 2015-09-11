for f in *.html
do 
	cat ../noCacheHeader.html > temp
	tail -n +5 $f >> temp
	mv temp  $f
done
