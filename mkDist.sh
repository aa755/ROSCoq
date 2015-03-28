rm -rf dist/
mkdir dist
mkdir dist/coq
mkdir dist/coq/CRMisc
mkdir dist/coq/IRMisc
cp *.v dist/coq/
cp SConstruct dist/coq/
cp site_scons/ dist/coq/
cp -r site_scons/ dist/coq/
cp -r shim dist/coq/
cp -r IRMisc/*.v dist/coq/IRMisc/
cp -r CRMisc/*.v dist/coq/CRMisc/
rm dist/coq/AngleMS.v 
rm dist/coq/trash.v 
rm dist/coq/CartAR.v 
rm dist/coq/CoList.v 
rm dist/coq/Process.v 
rm dist/coq/Everything.v 
rm dist/coq/CRMisc/ContField.v
rm dist/coq/CRMisc/PointWiseRing.v
