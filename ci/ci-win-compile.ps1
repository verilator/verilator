git clone --depth 1 https://github.com/lexxmark/winflexbison
cd winflexbison
mkdir build
cd build
cmake .. --install-prefix $PWD/../installflexbison
cmake --build . --config Release
cmake --install . --prefix $PWD/../installflexbison
cd ..
$Env:WIN_FLEX_BISON="$PWD/installflexbison"
cd ..
mkdir build
cd build
cmake .. --install-prefix $PWD/../install
cmake --build . --config Release
cmake --install . --prefix $PWD/../install
