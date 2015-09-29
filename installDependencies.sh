rm -rf dependencies
mkdir dependencies
cd dependencies ; git clone https://github.com/aa755/corn.git ; cd corn; git checkout  VCoq8.5; git submodule update --init --recursive; scons -j2 -k
# replace -j2 with -jN where N is the number of free cores on your machine. This is important because the last
# step takes a long time (several hours on a single core), but it is extremely parallelizable.
# -k is important, because not all of CoRN compiles with Coq 8.5 . But enough of it compiles to make ROSCoq work. 
# -k asks scons to keep going after an error.
