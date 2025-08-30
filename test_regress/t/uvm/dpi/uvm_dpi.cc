//----------------------------------------------------------------------
// Copyright 2010-2017 Mentor Graphics Corporation
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2013 NVIDIA Corporation
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

//
// Top-level file that includes all of the C/C++ files required
// by UVM
//
// The C code may be compiled by compiling this top file only,
// or by compiling individual files then linking them together.
//

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>
#include "uvm_dpi.h"

// Avoid -Wmissing-definitions
 int uvm_re_match(const char * re, const char *str);
 const char * uvm_glob_to_re(const char *glob);
 int uvm_hdl_check_path(char *path);
 int uvm_hdl_read(char *path, p_vpi_vecval value);
 int uvm_hdl_deposit(char *path, p_vpi_vecval value);
 int uvm_hdl_force(char *path, p_vpi_vecval value);
 int uvm_hdl_release_and_read(char *path, p_vpi_vecval value);
 int uvm_hdl_release(char *path);
 void push_data(int lvl,char *entry, int cmd);
 void walk_level(int lvl, int argc, char**argv,int cmd);
 const char *uvm_dpi_get_next_arg_c (int init);
 extern char* uvm_dpi_get_tool_name_c ();
 extern char* uvm_dpi_get_tool_version_c ();
 extern regex_t* uvm_dpi_regcomp (char* pattern);
 extern int uvm_dpi_regexec (regex_t* re, char* str);
 extern void uvm_dpi_regfree (regex_t* re);

#include "uvm_common.c"
#include "uvm_regex.cc"
#include "uvm_hdl.c"
#include "uvm_svcmd_dpi.c"

#ifdef __cplusplus
}
#endif
