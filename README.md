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

For the past few weeks, I have been writing a more general shim in Haskell using (my fork of) roshask:
https://github.com/aa755/roshask .
Then one can extract Coq programs to Haskell and then link it with the haskell shim.
Also, it would be then possible to use ROSCoq to program **any** robot supported by ROS. 
