if (-Not (Test-Path $PWD/../.ccache/win_bison.exe)) {
	git clone --depth 1 https://github.com/lexxmark/winflexbison
	cd winflexbison
	mkdir build
	cd build
	cmake .. --install-prefix $PWD/../../../.ccache
	cmake --build . --config Release -j 3
	cmake --install . --prefix $PWD/../../../.ccache
	cd ../..
}
mkdir build
cd build
cmake .. --install-prefix $PWD/../install
cmake --build . --config Release -j 3
cmake --install . --prefix $PWD/../install
