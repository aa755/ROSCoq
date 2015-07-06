# ROSCoq
Robots powered by Constructive Reals

This is a framework for writing and reasoning about Robotic programs in Coq. 
Our Coq programs are designed to actually run on robots using the Robot Operating System.
https://www.youtube.com/watch?v=3cV4Qr1-I0E&feature=youtu.be

For more details, please visit:
http://www.cs.cornell.edu/~aa755/ROSCoq/ 
Also, there are slides from a talk at the Coq workshop 2015
http://www.cs.cornell.edu/~aa755/ROSCoq/CoqWorkshop.pdf
If you use an annotation-aware PDF reader, e.g. Foxit, Adobe, you will notice that the slides have speech bubbles.
In these bubbles, have put down what I said (IIRC) while describing that slide.
Questions are welcome; please create an issue.


Status:

At this point, I think we have good support for reasoning about robotic systems.
However, more work needs to be done for running these programs on ROS supported robots.
There is an old shim written in ROSJava that only handles iCreate robots:
http://www.cs.cornell.edu/~aa755/ROSCoq/installation.html (the last 2 sections)

I plan to write a more general shim in Haskell using roshask:
https://github.com/acowley/roshask
The plan is to extract Coq programs to Haskell and then run  link it with the haskell shim.
I have an unrelated full-time job till the end of August, and untill then, I will be unable to find much time to work on ROSCoq.
However, starting september, my first priority will be to develop the above mentioned Haskell shim.
Pull Requests are welcome.

