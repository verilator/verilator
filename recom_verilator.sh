autoconf
export VERILATOR_ROOT=`pwd`   # if your shell is bash
./configure
make -j `nproc`
