mkdir -p rosjava
sudo apt-get install ros-indigo-catkin ros-indigo-rospack python-wstool
wstool init -j4 ~/rosjava/src https://raw.githubusercontent.com/rosjava/rosjava/indigo/rosjava.rosinstall
cd ~/rosjava/
rosdep update
rosdep install --from-paths src -i -y -r
catkin_make
cd src/
wstool merge https://raw.githubusercontent.com/me/rosinstalls/master/my_custom_msg_repos.rosinstall
catkin_create_rosjava_pkg rosjava_catkin_package_a
source devel/setup.bash
cd ..
source devel/setup.bash
cd src
catkin_create_rosjava_pkg rosjava_catkin_package_a
catkin_make
source devel/setup.bash
cd src/rosjava_catkin_package_a
catkin_create_rosjava_project my_pub_sub_tutorial
cd ../..
catkin_make
roscore

cd src/rosjava_catkin_package_a/my_pub_sub_tutorial
cd build/install/my_pub_sub_tutorial/bin
./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Talker &
./my_pub_sub_tutorial com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial.Listener
