export ROSCOQ_COQTOPOPTIONS="-R $HOME/dist/coq ROSCOQ -R $HOME/dist/dependencies/corn/math-classes/src MathClasses -R $HOME/dist/dependencies/corn CoRN"
export ROSCOQ_COQMESSAGEHANDLER=$HOME/dist/coq/icreateConcrete 
# do not include the filename extension (.v) in above
cd src/roscoqshim/my_pub_sub_tutorial/build/install/my_pub_sub_tutorial/bin ; ./my_pub_sub_tutorial com.github.rosjava.roscoqshim.my_pub_sub_tutorial.ROSCoqShim
