ls
sudo apt-get install scons git ocaml camlp5 liblablgtk2-ocaml-dev
history -a
ls
git clone https://github.com/coq/coq.git
cd coq
git checkout v8.4
./configure 
make -j4
sudo make install
history -a
cd ..
mkdir ROSCoqDep
git clone https://github.com/aa755/ROSCoq.git
mv ROSCoq/installDependencies.sh ./
vim installDependencies.sh 
sudo apt-get install vim
cd ROSCoqDep
ls
git clone https://github.com/aa755/ROSCoq.git
mv ROSCoq/installDependencies.sh ./
./installDependencies.sh 
cd ../coq/
ls
git log
gt branch -a
git branch -a
cd ../ROSCoq
cd ..
rm -rf ROSCoq
cd ROSCoqDep/dependencies/
ls
cd corn/
ls
git log
cd math-classes/
ls
git log
coqc --ver
coqc --version
cd ..
ls
history -a
cd ..
ls
cd ROSCoq/
ls
cp SConstruct.dist SConstruct
scons
ls ../dependencies/corn/transc/ArTanH.vo
ls ../dependencies/corn/transc/ArTanH.v
/home/abhishek/ROSCoqDep/dependencies/corn/transc/ArTanH.vo
cd /home/abhishek/ROSCoqDep/dependencies/corn/
scons transc/ArTanH.vo
cd ../../
ls
cd ROSCoq/
ls
scons -j3
cd -
cd dependencies/corn/
scons /transc/SinCos.vo
scons transc/SinCos.vo
cd ../../ROSCoq/
scons 
cd -
scons transc/Pi.vo
cd -
scons
cd -
scons transc/TrigMon.vo
cd -
scons
cd -
scons transc/MoreArcTan.vo
cd -
scons
cd -
scons
scons reals/fast/CRtrans.v 
scons reals/fast/CRtrans.v
scons reals/fast/CRtrans.vo
scons reals/fast/CRtrans.vo -j3
cd -
scons
scons -j3
cd -
scons reals/fast/ARtrans.vo -j3
scons reals/faster/ARtrans.vo -j3
cd -
scons -j3
cd -
scons reals/faster/ARbigD.vo -j3
cd -
scons 
scons -j4
cd -
scons ftc/IntegrationRules.vo
cd -
scons -j3
cp home:/ice
history -a
git pull
git config --global user.email "abhishek.anand.iitg@gmail.com"
git config --global user.name "Abhishek Anand (@VM inside MSR desktop)"
git pull
git log
scons
wget https://raw.githubusercontent.com/coq/coq/trunk/plugins/extraction/ExtrHaskellBasic.v
scons
scons -j3
git diff --color
ls -lrt extraction/roboExtract.ml 
cat icreateConcreteOCaml.ml
cat icreateConcreteOCaml.v
rm extraction/roboExtract.ml 
scons icreateConcreteOCaml.vo
vim icreateConcreteOCaml.v
gedit icreateConcreteOCaml.v
scons icreateConcreteOCaml.vo
git diff --color
cd extraction/
ocamlc roboExtract.ml
rm roboExtract.mlo
rm roboExtract.mli
ocamlc roboExtract.ml
gedit icreateConcreteOCaml.v
cd ..
gedit icreateConcreteOCaml.v
scons icreateConcreteOCaml.vo
gedit icreateConcreteOCaml.v
scons icreateConcreteOCaml.vo
git diff --color
cd extraction/
git checkout roboExtract.ml
ocamlc roboExtract.ml
rm roboExtract.mlo
rm roboExtract.mli
ocamlc roboExtract.ml
cd ..
gedit icreateConcreteOCaml.v
scons icreateConcreteOCaml.vo
git diff --color
git status
scp icreateConcreteOCaml.v home:
mkdir ~/host
suto mount -t vboxsf shared ~/host
sudo mount -t vboxsf shared ~/host
cp icreateConcreteOCaml.v ~/host/
history -a
