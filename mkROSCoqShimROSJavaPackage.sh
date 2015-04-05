set -e
cd rosjava
source devel/setup.bash
cd src
catkin_create_rosjava_pkg roscoqshim
cd roscoqshim
catkin_create_rosjava_project my_pub_sub_tutorial
cd my_pub_sub_tutorial/src/main/java/com/github/roscoqshim/my_pub_sub_tutorial/
rm *.java
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/ROSCoqShim.java
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/ICreateDriverNoRep.java
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/ExternalAgent.java
cd ~/rosjava
catkin_make
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/runDriver.sh
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/runShim.sh
wget http://www.cs.cornell.edu/~aa755/ROSCoq/Shim/runExternalAgent.sh

#cd src/rosjava_catkin_package_a/my_pub_sub_tutorial
#cd build/install/my_pub_sub_tutorial/bin
#./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Talker &
#./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Listener
