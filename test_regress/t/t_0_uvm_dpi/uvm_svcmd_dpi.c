//
//------------------------------------------------------------------------------
// Copyright 2010-2012 AMD
// Copyright 2011-2018 Cadence Design Systems, Inc.
// Copyright 2011-2014 Mentor Graphics Corporation
// Copyright 2013-2024 NVIDIA Corporation
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
//------------------------------------------------------------------------------

//----------------------------------------------------------------------
// Git details (see DEVELOPMENT.md):
//
// $File$
// $Rev$
// $Hash$
//
//----------------------------------------------------------------------


#include "uvm_dpi.h"
#include <assert.h>

#define ARGV_STACK_PTR_SIZE 32

// the total number of arguments (minus the -f/-F minus associated filenames) 
int argc_total;
// the ptr to the array of ptrs to the args
char** argv_stack=NULL;

char ** argv_ptr=NULL;


void push_data(int lvl,char *entry, int cmd) {
  if(cmd==0)
    argc_total++;
  else
    *argv_ptr++=entry;
}

// walk one level (potentially recursive)
void walk_level(int lvl, int argc, char**argv,int cmd) {
    int idx;
    for(idx=0; ((lvl==0) && idx<argc) || ((lvl>0) && (*argv));idx++,argv++) {
      if(strcmp(*argv, "-f") && strcmp(*argv, "-F")) {
	push_data(lvl,*argv,cmd);	
      } else {
	argv++;
	idx++;
	char **n=(char**) *argv;
	walk_level(lvl+1,argc,++n,cmd);
      }
    }
}

const char *uvm_dpi_get_next_arg_c (int init) {
	s_vpi_vlog_info info;
	static int idx=0;

	if(init==1)
	{
		// free if necessary
		free(argv_stack);
		argc_total=0;

		vpi_get_vlog_info(&info);
		walk_level(0,info.argc,info.argv,0);

		argv_stack = (char**) malloc (sizeof(char*)*argc_total);
		argv_ptr=argv_stack;
		walk_level(0,info.argc,info.argv,1);	
		idx=0;	
		argv_ptr=argv_stack;
	}

	if(idx++>=argc_total)
	  return NULL;
	
	return *argv_ptr++;
}

extern char* uvm_dpi_get_tool_name_c ()
{
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return info.product;
}

extern char* uvm_dpi_get_tool_version_c ()
{
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return info.version;
}

