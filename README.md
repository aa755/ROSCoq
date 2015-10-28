# ROSCoq
Robots powered by Constructive Reals

This is a framework for writing and reasoning about Robotic programs in Coq. 
Our Coq programs are designed to actually run on robots using the Robot Operating System.
https://www.youtube.com/watch?v=3cV4Qr1-I0E&feature=youtu.be  
For more conceptual details, please read the paper
http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf

Also, there are slides from a talk at ITP 2015:  
http://www.cs.cornell.edu/~aa755/ROSCoq/ITP.pdf

For instructions on installing and using ROSCoq, please visit the wiki:
https://github.com/aa755/ROSCoq/wiki    
Questions are welcome; please create an issue, or ask me directly.

Updates since the ITP15 submission:

I have written a more general [shim in Haskell](https://github.com/aa755/ROSCoq/tree/master/src/shim/Haskell) using (my fork of) roshask:  
https://github.com/aa755/roshask  
One can now extract Coq programs to Haskell and then link it with the haskell shim.
It should be now possible to use ROSCoq to program **any** robot supported by ROS.

