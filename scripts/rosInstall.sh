set -e
sudo sh -c 'echo "deb http://packages.ros.org/ros/ubuntu trusty main" > /etc/apt/sources.list.d/ros-latest.list'
wget https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -O - | sudo apt-key add -
sudo apt-get update
sudo apt-get install ros-indigo-desktop-full 
sudo rosdep init
rosdep update
echo "source /opt/ros/indigo/setup.bash" >> ~/.bashrc
source ~/.bashrc 

# Skip the parts below if you do not have an actual iRobot Create.
# Below, we assume that the iRobot create device is connected to the computer at the port /dev/ttyUSB0. 
# On your machine, it might be /dev/ttyUSB1 or /dev/ttyUSB2 ... (especially if you have multiple USB devices connected). 
# One way to find out is to see the difference between the output of ls /dev/ttyUSB* before and after connecting the iRobot Create via USB. 
# If needed, replace the two occurrences of /dev/ttyUSB0 below.
sudo apt-get install ros-indigo-turtlebot ros-indigo-turtlebot-bringup
sudo adduser $USER dialout
echo "export TURTLEBOT_BASE=create" >> ~/.bashrc
echo "export TURTLEBOT_SERIAL_PORT=/dev/ttyUSB0" >> ~/.bashrc
echo "export TURTLEBOT_STACKS=circles" >> ~/.bashrc
sudo chmod a+rw /dev/ttyUSB0
source ~/.bashrc 

#roscore
#roslaunch turtlebot_bringup minimal.launch
#rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist '[0.1, 0, 0]' '[0, 0, 0]' && rostopic pub -1 /cmd_vel_mux/input/navi geometry_msgs/Twist  -- '[0, 0, 0]' '[0, 0, 0]'
