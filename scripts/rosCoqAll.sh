set -e
wget www.cs.cornell.edu/~aa755/ROSCoq/dist.zip 
unzip dist.zip 
cd dist 
bash -x installDependencies.sh 
cd coq 
scons 