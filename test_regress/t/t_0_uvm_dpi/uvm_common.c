//----------------------------------------------------------------------
// Copyright 2010 AMD
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2013-2024 NVIDIA Corporation
// Copyright 2010-2013 Synopsys, Inc.
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

//----------------------------------------------------------------------
// Git details (see DEVELOPMENT.md):
//
// $File$
// $Rev$
// $Hash$
//
//----------------------------------------------------------------------


// Implementation of common methods for DPI

extern void m__uvm_report_dpi(int,const char*,const char*,int,const char*, int);

#if defined(XCELIUM) || defined(NCSC)
const static char* uvm_package_scope_name = "uvm_pkg::";
#else
const static char* uvm_package_scope_name = "uvm_pkg";
#endif

void m_uvm_report_dpi( int severity,
		char* id,
		char* message,
		int verbosity,
		char* file,
		int linenum) {
  svScope old_scope = svSetScope(svGetScopeFromName(uvm_package_scope_name));
  m__uvm_report_dpi(severity, id, message, verbosity, file, linenum);
  svSetScope(old_scope);
 }


int int_str_max ( int radix_bits ) {
    int val = INT_MAX;
    int ret = 1;
    while ((val = (val /radix_bits)))
        ret++;
    return ret;
}
