set -e
sudo sh -c 'echo "deb http://packages.ros.org/ros/ubuntu trusty main" > /etc/apt/sources.list.d/ros-latest.list'
wget https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -O - | sudo apt-key add -
sudo apt-get update
sudo apt-get install ros-indigo-desktop-full ros-indigo-turtlebot ros-indigo-turtlebot-bringup
sudo rosdep init
rosdep update
sudo adduser $USER dialout
echo "source /opt/ros/indigo/setup.bash" >> ~/.bashrc
echo "export TURTLEBOT_BASE=create" >> ~/.bashrc
echo "export TURTLEBOT_SERIAL_PORT=/dev/ttyUSB0" >> ~/.bashrc
echo "export TURTLEBOT_STACKS=circles" >> ~/.bashrc
source ~/.bashrc 
sudo chmod a+rw /dev/ttyUSB0
#roscore
#roslaunch turtlebot_bringup minimal.launch
#rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]' && rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist  -- '[0, 0, 0]' '[0, 0, 0]'
