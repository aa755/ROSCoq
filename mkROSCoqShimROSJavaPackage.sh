set -e
cd roskava/src
catkin_create_rosjava_pkg ROSCoqShim
source devel/setup.bash
cd src/ROSCoqShim
catkin_create_rosjava_project my_pub_sub_tutorial
cd ../..
catkin_make

#cd src/rosjava_catkin_package_a/my_pub_sub_tutorial
#cd build/install/my_pub_sub_tutorial/bin
#./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Talker &
#./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Listener
