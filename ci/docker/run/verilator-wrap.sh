#!/bin/bash
# DESCRIPTION: Wrap a Verilator call and copy vlt includes
#              (inside docker container)
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

perl /usr/local/bin/verilator "$@"
status=$?
if [ $status -ne 0 ]; then
    exit $status
fi

# Check if user set an obj_dir
obj_dir=$(echo " $@" | grep -oP '\s--Mdir\s*\K\S+')
if [ "$obj_dir" == "" ]; then
    obj_dir="obj_dir"
fi

# If the run was successful: Copy required files to allow build without this container
if [ -e ${obj_dir} ]; then
    # Copy files required for the build
    mkdir -p ${obj_dir}/vlt
    cp -r /usr/local/share/verilator/bin ${obj_dir}/vlt
    cp -r /usr/local/share/verilator/include ${obj_dir}/vlt
    # Point Makefile to that folder
    sed -i 's/VERILATOR_ROOT = \/usr\/local\/share\/verilator/VERILATOR_ROOT = vlt/g' ${obj_dir}/*.mk
fi
