set -e
mkdir -p rosjava
sudo apt-get install ros-indigo-catkin ros-indigo-rospack python-wstool
wstool init -j4 ~/rosjava/src https://raw.githubusercontent.com/rosjava/rosjava/indigo/rosjava.rosinstall
cd ~/rosjava/
rosdep update
rosdep install --from-paths src -i -y -r
catkin_make
cd src/
wstool merge https://raw.githubusercontent.com/me/rosinstalls/master/my_custom_msg_repos.rosinstall
