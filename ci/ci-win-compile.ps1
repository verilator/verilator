# DESCRIPTION: Verilator: CI Windows Power Shell - Compile Verilator
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
################################################################################

Set-PSDebug -Trace 1

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
