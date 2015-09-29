rm -rf dependencies
mkdir dependencies
cd dependencies ; git clone https://github.com/aa755/corn.git ; cd corn; git checkout  VCoq8.5; git submodule update --init --recursive; scons -j2
# replace -j2 with -jN where N is the number of free cores on your machine. This is important because the last
# step takes a long time (several hours on a single core), but it is extremely parallelizable.
