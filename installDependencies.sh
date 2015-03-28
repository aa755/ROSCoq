rm -rf dependencies
mkdir dependencies
cd dependencies ; git clone https://github.com/c-corn/corn.git ; cd corn; git checkout d829dc968878aee1bcf944ac470ac03fc3b670a5 -b ROSCoq; git submodule update --init --recursive; scons
