cd install
$Env:VERILATOR_ROOT=$PWD
cd examples/cmake_tracing_c
mkdir build
cd build
cmake ..
cmake --build . --config Release -j 3
Release/example.exe
cd ..
Remove-Item -path build -recurse
