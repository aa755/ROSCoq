# ROSCoq
Robots powered by Constructive Reals

This is a framework for writing and reasoning about Robotic programs in Coq. 
Our Coq programs are designed to actually run on robots using the Robot Operating System.
https://www.youtube.com/watch?v=3cV4Qr1-I0E&feature=youtu.be

For more details, please visit:
http://www.cs.cornell.edu/~aa755/ROSCoq/ 

Also, there are slides from a talk at ITP 2015:
http://www.cs.cornell.edu/~aa755/ROSCoq/ITP.pdf

Questions are welcome; please create an issue, or ask me directly.


Status:

At this point, I think we have good support for reasoning about robotic systems.
However, more work needs to be done for running these programs on ROS supported robots.
There is an old shim written in ROSJava that only handles iCreate robots:
http://www.cs.cornell.edu/~aa755/ROSCoq/installation.html (the last 2 sections)

I am writing a more general shim in Haskell using (my fork of) roshask:
https://github.com/aa755/roshask
Then one can extract Coq programs to Haskell and then run  link it with the haskell shim.


Pull Requests are welcome.
Here are some remaining substeps for that shim. If anyone wants to work on any of these substeps, or has any suggestions, please let me know.

1) Modify roshask code so that it also emites Coq definitions for ROS message data-types. Currently it produces (only) Haskell definitions. Here is an example ROS message type,
and its definitions in Haskell and Coq:

http://docs.ros.org/api/std_msgs/html/msg/String.html

https://github.com/aa755/ROSCoq/blob/bbc63a39163b8df2e287673fc769f0f77529be21/src/shim/Haskell/examples/String.hs

https://github.com/aa755/ROSCoq/blob/bbc63a39163b8df2e287673fc769f0f77529be21/src/shim/Haskell/ROSStringMsg.v 


2) testing.

