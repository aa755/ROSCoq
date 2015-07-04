# tested on a fresh install of Ubuntu 15.04
# This script often prompts for interactive confirmations or sudo passwords. Always selecting the default choice should work.

# Install Coq 8.4 tip
sudo apt-get install scons git ocaml camlp5 liblablgtk2-ocaml-dev
git clone https://github.com/coq/coq.git
cd coq
git checkout v8.4
./configure 
make -j4
sudo make install
cd ..

# download ROSCoq
mkdir ROSCoqDep
cd ROSCoqDep
git clone https://github.com/aa755/ROSCoq.git


# install a version of CoRN known to work with ROSCoq.
mkdir dependencies
cd dependencies 
git clone https://github.com/c-corn/corn.git 
cd corn
git checkout d829dc968878aee1bcf944ac470ac03fc3b670a5 -b ROSCoq
git submodule update --init --recursive
scons -k -j4 # -k is needed because some parts of CoRN do not compile with Coq 8.4 tip. Fortunately enough of CoRN compiles.

cd ../../ROSCoq
wget https://raw.githubusercontent.com/coq/coq/trunk/plugins/extraction/ExtrHaskellBasic.v
scons -j4
