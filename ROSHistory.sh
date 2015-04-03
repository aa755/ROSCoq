
sudo sh -c 'echo "deb http://packages.ros.org/ros/ubuntu trusty main" > /etc/apt/sources.list.d/ros-latest.list'
sudo apt-get update
wget https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -O - | sudo apt-key add -
sudo apt-get update
sudo apt-get install ros-indigo-desktop-full
sudo rosdep init
rosdep update
history -a
rosnode list
sudo adduser abhishek dialout
sudo adduser gunjan dialout
roslaunch turtlebot_bringup minimal.launch
sudo apt-get install ros-indigo-turtlebot
sudo apt-get install ros-indigo-turtlebot-bringup 
roslaunch turtlebot_bringup minimal.launch
vim ~/.bashrc
echo "export TURTLEBOT_BASE=create" >> ~/.bashrc
echo "export TURTLEBOT_SERIAL_PORT=/dev/ttyUSB0" >> ~/.bashrc
history -a
vim ~/.bashrc 
roslaunch turtlebot_bringup minimal.launch
vim ~/.bashrc 
source ~/.bashrc 
roslaunch turtlebot_bringup minimal.launch
echo "export TURTLEBOT_STACKS=circles" >> ~/.bashrc
source ~/.bashrc 
roslaunch turtlebot_bringup minimal.launch
sudo chmod a+rw /dev/ttyUSB0
history -a
rostopic list
rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]' && rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist  -- '[0, 0, 0]' '[0, 0, 0]'
history -a
vim bookmark.txt
ls
cd turtlebot/
ls
cp goforward.py
cp goforward.py roscoq1.py
vim roscoq1.py
rostopic list
vim roscoq1.py
vim ~/.bash_history
ls
coqc -v
git clone --recursive https://github.com/c-corn/corn.git
git log
cd corn
ls
git log
git checkout -b 640b95668956b452a85938136c43fb0b686dca7d preOpam
git checkout 640b95668956b452a85938136c43fb0b686dca7d -b preOpam
git log
scons -j3
sudo apt-get install scons
scons 
ls
git log
scons
cd math-classes/
ls
git submodule update --init --recursive
ls
cd ..
scons
scons -j2
scons -j4
scons -j2
roslaunch turtlebot_bringup minimal.launch
echo "source /opt/ros/indigo/setup.bash" >> ~/.bashrc
source ~/.bashrc
sudo apt-get install ros-indigo-turtlebot-create
roscore
cd turtlebot
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
cd src/rosjava_catkin_package_a/my_pub_sub_tutorial
cd ../rosjava/
cd src/rosjava_catkin_package_a/my_pub_sub_tutorial
cd build/install/my_pub_sub_tutorial/bin
./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Talker &
./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Listener
sudo apt-get install ros-indigo-rosjava
sudo apt-get update
sudo apt-get install ros-indigo-rosjava
rosjava
apt-cache search rosjava
sudo apt-get install ros-indigo-catkin ros-indigo-rospack python-wstool
wstool init -j4 ~/rosjava/src https://raw.githubusercontent.com/rosjava/rosjava/indigo/rosjava.rosinstall
cd ~/rosjava/
rosdep update
rosdep install --from-paths src -i -y -r
catkin_make
ls
cd src/
ls
wstool merge https://raw.githubusercontent.com/me/rosinstalls/master/my_custom_msg_repos.rosinstall
catkin_create_rosjava_pkg rosjava_catkin_package_a
source devel/setup.bash
cd ..
source devel/setup.bash
%catkin_create_rosjava_pkg rosjava_catkin_package_a
cd src
%catkin_create_rosjava_pkg rosjava_catkin_package_a
catkin_create_rosjava_pkg rosjava_catkin_package_a
ls
catkin_make
cd ..
catkin_make
source devel/setup.bash
cd src/rosjava_catkin_package_a
catkin_create_rosjava_project my_pub_sub_tutorial
cd ../..
catkin_make
history -a
vim rosjavaInstall.sh
sudo vim /etc/fstab
cat bookmark.txt 
git clone https://github.com/markwsilliman/turtlebot/
cd turtlebot
python goforward.py
sudo apt-get install ros-indigo-rospy
python goforward.py
sudo apt-get install ros-indigo-rospy-message-converter 
python goforward.py
catkin_make
ls
rosrun goforward.py 
rosnode list
source ~/.bashrc 
rosnode list
python goforward.py
tail -f ~/.bash_history 
rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic help pub
rostopic pub -h
rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic pub 10 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic pub -r 10 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
python goforward.py
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
vim roscoq1.py 
python roscoq1.py 
cd ..
cd -
sudo reboot
top
roscore
cd ../rosjava/
cd src/
ls
cd rosjava_catkin_package_a/
ls
cd my_pub_sub_tutorial/
ls
cd src/
ls
cd main/
ls
cd java
ls
cd com
ls
cd github
ls
cd rosjava_catkin_package_a/
ls
cd my_pub_sub_tutorial/
ls
vim Listener.java 
rostopic list
rostopic help
rostopic type /mobile_base/commands/velocity 
cd ..
ls *.sh
vim rosInstall.sh 
cat rosInstall.sh 
rostopic pub -1 /mobile_base/commands/velocity geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic help
rostopic help pub
rostopic  pub -h
rostopic pub -1 /mobile_base/commands/velocity geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]'
rostopic echo mobile_base/commands/velocity
cd rosjava/
ls
catkin_make
cd ~/rosjava/
catkin_make
cd ../rosjava/
ls
cd src/
ls
cd rosjava_catkin_package_a/
ls
cd my_pub_sub_tutorial/
ls
cd src/
ls
cd main/
ls
cd java/
ls
cd com/
ls
cd github/
ls
cd rosjava_catkin_package_a/
ls
cd my_pub_sub_tutorial/
ls
cd
cd turtlebot/
ls
python goforward.py
vim goforward.py
python goforward.py
vim goforward,py
vim goforward.py
rostopic list
rostopic echo /mobile_base/commands/velocity
cat ../rosInstall.sh 
rostopic list
rostopic pub -1 /icreate_vel '[0.1, 0, 0]'
rostopic pub -1 /icreate_vel Vector3 '[0.1, 0, 0]'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '[0.1, 0, 0]'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 [0.1, 0, 0]
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 ['0.1', '0', '0']
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '[0.1, 0.0, 0.0]'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0.1, 0.0, 0.0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0.1','0.0', '0.0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0.1' , '0.0', '0.0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0.1' , '0.0' , '0.0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0.1' '0' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0.1' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '-0.1' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '- 0.1' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0.1' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0' '0'
./runCoqtop.sh 
source devel/setup.bash 
catkin_make
./run.sh 
catkin_make
cat run.sh 
cp run.sh runDriver.sh
mv run.sh runCoqtop.sh
vim runCoqtop.sh
./runDriver.sh 
catkin_make
./runDriver.sh 
rostopic echo icreate_vel
rostopic pub -1 /mobile_base/commands/velocity geometry_msgs/Twist '[0, 0, 0]' '[0.5, 0, 0]'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0.5' '0'
rostopic pub -1 /icreate_vel geometry_msgs/Vector3 '0' '0' '0'
rostopic help 
rostopic pub -h
rostopic echo icreate_vel
sudo reboot
cd
cd rosjava/
ls
cd build/
ls
cd rosjava_core/
ls
cd catkin_generated/
ls
cd installspace/
ls
cd ..
ls
cd ..
ls
cd ..
ls
cd catkin
ls
cd catkin_generated/
ls
cd version/
ls
cd ..
ls
cd ..
cd devel/
ls
cd lib/
ls
cd ../include/
ls
cd rosgraph_msgs/
ls
cd ..
ls
cd ..
ls
cd ..
find -name *.jar
cd build/
ls
cd rosjava_core/
ls
cd ../rosjava_messages/
ls
cd ..
catkin_make
vim rosjavaInstall.sh 
source devel/setup.bash 
catkin_mak
catkin_make
ls
cat rosjavaInstall.sh 
vim run.sh
chmod +x run.sh 
./run.sh 
rostopic list
catkin_make
./run.sh 
catkin_make
./run.sh 
cd ..
df -h
ls
cd coq
ls
cd ..
ls
cd padhai/
ls
cd ..
ls -f
ls -d
ls -d *
ls Office/
ls
ls Office/
mkdir padhaiLocal
cd padhai
cd ..
cd padhaiLocal/
git clone file://home/gunjan/padhai
git clone file://home/gunjan/padhai/
git clone file://home/gunjan/padhai.git
git clone file://home/gunjan/padhai/git
git clone file:///home/gunjan/padhai
ls
cd padhai/
ls
cd coq/
ls
cd ROSCOQ/
ls
mkdir shim
ls
cd shim/
ls
cp ../../../../../rosjava/src/rosjava_catkin_package_a/my_pub_sub_tutorial/src/main/java/com/github/rosjava_catkin_package_a/my_pub_sub_tutorial/* ./
ls
git add Listener.java 
git add *.java 
git commit -a
git push
vim update.sh
chmod +x update.sh 
./update.sh 
git commit -a
./update.sh 
git commit -a
git push
cd .
cd ..
scons 
vim AngleMS.v
scons 
scons
ls CRMisc/
vim AngleMS.v
scons -c
vim AngleMS.v
scons 
cd ..
mv padhaiLocal/padhai padhaiWC
ls padhaiLocal/
rm -rf  padhaiLocal/
ls
cd padhaiW
cd padhaiWC/
ls
cd coq/ROSCOQ/
ls
scons
cd ../..
ls
cd ..
mv corn ssrcorn
cd -
cd coq/ROSCOQ/
scons
scons -j2
git pull
scons
git pull
scons
coqtop
coqtop -R . ROSCOQ -R ../../../ssrcorn/math-classes/src MathClasses -R ../../../ssrcorn CoRN
cd shim/
./update.sh 
ls
./update.sh 
ls
vim update.sh 
./update.sh 
git commit -a
git push
./update.sh 
git commit -a
git push
cd ~/Downloads/
ls
chmod +x netbeans-8.0.2-javase-linux.sh 
./netbeans-8.0.2-javase-linux.sh 
cd ../turtlebot/
ls
gedit goforward.py
rostopiv list
rostopic list
roslaunch turtlebot_bringup minimal.launch
roscore
cat gunjanKey.pub >>~/.ssh/authorized_keys 
vim ~/.ssh/authorized_keys 
sudo apt-get install openmovieeditor
sudo apt-get install lucid
apt-cache search movie
apt-cache search movieeditor
apt-cache search moviemaker
apt-cache search movie
apt-cache search movie maker
apt-cache search movie editor
sudo apt-get install pitivi
pitvi
pitivi
apt-cache search movie editor
coqc -v
lsb_release -a
ls *.sh
./checkfreespace.sh 
ls
coqide
cd padhaiWC/
git pull
ls
cd coq/
ls
cd ROSCOQ/
ls
./mkDist.sh 
vim mkDist.sh 
cat mkDist.sh 
bash -x mkDist.sh 
ls
cd dist/
ls
cd ..
ls
cp SConstruct SConstruct.dist
vim SConstruct.dist
vim mkDist.sh 
vim installDependencies.sh
cp installDependencies.sh dist/
ls
cd dist/
chmod +x installDependencies.sh 
./installDependencies.sh 
ls
cd dependencies/
ls
cd corn/
cat ../../installDependencies.sh 
cd ..
rm -rf dependencies/
vim installDependencies.sh 
./installDependencies.sh 
cd dependencies/corn/
scons -j3
cd ..
cd coq
scons -j3
vim SConstruct 
cd ..
git pull
cp *.v dist/
cp SConstruct.dist dist/coq/
vim SConstruct.dist 
cd dist/coq/
scons -j3
vim SConstruct
cd ../../
cp SConstruct.dist dist/coq/SConstruct
cd -
scons
scons -j3
bash coqidescript.sh icreate.v
cd
mkdir router
cd router/
vim key,pub
rm key,pub
vim key.pub
gedit key.pub 
ipconfig
ifconfig
python -v
python --version
iftop
sudo apt-get install iftop
iftop -i 
ifconfig
iftop -i eth0
sudo iftop -i eth0
