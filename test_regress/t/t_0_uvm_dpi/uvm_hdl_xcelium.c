//----------------------------------------------------------------------
// Copyright 2007-2023 Cadence Design Systems, Inc.
// Copyright 2009-2011 Mentor Graphics Corporation
// Copyright 2013-2024 NVIDIA Corporation
// Copyright 2010-2011 Synopsys, Inc.
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


// use -DINCA_EXTENDED_PARTSEL_SUPPORT to use extended support for vpi_handle_by_name

#include "vhpi_user.h"
#include "vpi_user.h"
#include "veriuser.h"
#include "svdpi.h"
#include <malloc.h>
#include <string.h>
#include <stdio.h>

static void m_uvm_error(const char *ID, const char *msg, ...);
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static void m_uvm_get_object_handle(const char* path, vhpiHandleT *handle,int *language);
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static int uvm_hdl_max_width();

// static print buffer
static char m_uvm_temp_print_buffer[1024];

/* 
 * UVM HDL access C code.
 *
 */
static void m_uvm_get_object_handle(const char* path, vhpiHandleT *handle,int *language)
{
  *handle = vhpi_handle_by_name(path, 0);

  if(*handle)
	  *language = vhpi_get(vhpiLanguageP, *handle);
}

// returns 0 if the name is NOT a slice
// returns 1 if the name is a slice
static int is_valid_path_slice(const char* path) {
	  char *path_ptr = (char *) path;
	  int path_len;

#ifdef INCA_EXTENDED_PARTSEL_SUPPORT
	  return 0;
#endif

	  path_len = strlen(path);
	  path_ptr = (char*)(path+path_len-1);

	  if (*path_ptr != ']')
	    return 0;

	  while(path_ptr != path && *path_ptr != ':' && *path_ptr != '[')
	    path_ptr--;

	  if (path_ptr == path || *path_ptr != ':')
	    return 0;

	  while(path_ptr != path && *path_ptr != '[')
	    path_ptr--;

	  if (path_ptr == path || *path_ptr != '[')
	    return 0;

	  return 1;
}

static int uvm_hdl_set_vlog_partsel(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  char *path_ptr = path;
  int path_len;
  svLogicVecVal bit_value;

  if(!is_valid_path_slice(path)) return 0;
  path_len = strlen(path);
  path_ptr = (char*)(path+path_len-1);

  if (*path_ptr != ']')
    return 0;

  while(path_ptr != path && *path_ptr != ':' && *path_ptr != '[')
    path_ptr--;

  if (path_ptr == path || *path_ptr != ':')
    return 0;

  while(path_ptr != path && *path_ptr != '[')
    path_ptr--;

  if (path_ptr == path || *path_ptr != '[')
    return 0;

  int lhs, rhs, width, incr;

  // extract range from path
  if (sscanf(path_ptr,"[%u:%u]",&lhs, &rhs)) {
    char index_str[20];
    int i;
    path_ptr++;
    path_len = (path_len - (path_ptr - path));
    incr = (lhs>rhs) ? 1 : -1;
    width = (lhs>rhs) ? lhs-rhs+1 : rhs-lhs+1;

    // perform set for each individual bit
    for (i=0; i < width; i++) {
      sprintf(index_str,"%u]",rhs);
      strncpy(path_ptr,index_str,path_len);
      svGetPartselLogic(&bit_value,value,i,1);
      rhs += incr;
      if (uvm_hdl_set_vlog_partsel(path,&bit_value,flag)==0) {
    	  if(uvm_hdl_set_vlog(path,&bit_value,flag)==0) { return 0; };
      }
    }
    return 1;
  }
  return 0;
}


/*
 * Given a path with part-select, break into individual bit accesses
 * path = pointer to user string
 * value = pointer to logic vector
 * flag = deposit vs force/release options, etc
 */
static int uvm_hdl_get_vlog_partsel(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  char *path_ptr = path;
  int path_len;
  svLogicVecVal bit_value;

  path_len = strlen(path);
  path_ptr = (char*)(path+path_len-1);

  if (*path_ptr != ']')
    return 0;

  while(path_ptr != path && *path_ptr != ':' && *path_ptr != '[')
    path_ptr--;

  if (path_ptr == path || *path_ptr != ':')
    return 0;

  while(path_ptr != path && *path_ptr != '[')
    path_ptr--;

  if (path_ptr == path || *path_ptr != '[')
    return 0;

  int lhs, rhs, width, incr;

  // extract range from path
  if (sscanf(path_ptr,"[%u:%u]",&lhs, &rhs)) {
    char index_str[20];
    int i;
    path_ptr++;
    path_len = (path_len - (path_ptr - path));
    incr = (lhs>rhs) ? 1 : -1;
    width = (lhs>rhs) ? lhs-rhs+1 : rhs-lhs+1;
    bit_value.aval = 0;
    bit_value.bval = 0;
    for (i=0; i < width; i++) {
      sprintf(index_str,"%u]",rhs);
      strncpy(path_ptr,index_str,path_len);

      if(uvm_hdl_get_vlog_partsel(path,&bit_value,flag) == 0) {
    	  if(uvm_hdl_get_vlog(path,&bit_value,flag)==0) { return 0; }
      }

      svGetBitselLogic(&bit_value,0);
      svPutPartselLogic(value,bit_value,i,1);
      rhs += incr;
    }
    return 1;
  } else {
	  return 0;
  }
}

static void clear_value(p_vpi_vecval value) {
    int chunks;
    int maxsize = uvm_hdl_max_width();
    chunks = (maxsize-1)/32 + 1;
    for(int i=0;i<chunks-1; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
}

/*
 * This C code checks to see if there is PLI handle
 * with a value set to define the maximum bit width.
 *
 * This function should only get called once or twice,
 * its return value is cached in the caller.
 *
 */
static int UVM_HDL_MAX_WIDTH = 0;
static int uvm_hdl_max_width()
{
  if(!UVM_HDL_MAX_WIDTH) {
    vpiHandle ms;
    s_vpi_value value_s = { vpiIntVal, { 0 } };
    ms = vpi_handle_by_name((PLI_BYTE8*) "uvm_pkg::UVM_HDL_MAX_WIDTH", 0);
    vpi_get_value(ms, &value_s);
    UVM_HDL_MAX_WIDTH= value_s.value.integer;
  } 
  return UVM_HDL_MAX_WIDTH;
}


/*
 * Given a path, look the path name up using the PLI,
 * and set it to 'value'.
 */
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  vpiHandle r;
  s_vpi_value value_s = { vpiIntVal, { 0 } };
  s_vpi_time  time_s = { vpiSimTime, 0, 0, 0.0 };

  r = vpi_handle_by_name(path, 0);

  if(r == 0)
    {
      m_uvm_error("UVM/DPI/HDL_SET","set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name",
	      path);
      return 0;
    }
  else
    {
      if(maxsize == -1) 
        maxsize = uvm_hdl_max_width();

      if (flag == vpiReleaseFlag) {
	// FIXME
	//size = vpi_get(vpiSize, r);
	//value_p = (p_vpi_vecval)(malloc(((size-1)/32+1)*8*sizeof(s_vpi_vecval)));
	//value = &value_p;
      }
      value_s.format = vpiVectorVal;
      value_s.value.vector = value;
      vpi_put_value(r, &value_s, &time_s, flag);  
      //if (value_p != NULL)
      //  free(value_p);
      if (value == NULL) {
	value = value_s.value.vector;
      }
    }

  vpi_release_handle(r);

  return 1;
}

static vhpiEnumT vhpiEnumTLookup[4] = {vhpi0,vhpi1,vhpiZ,vhpiX}; // idx={b[0],a[0]}
static vhpiEnumT vhpi2val(int aval,int bval) {
  int idx=(((bval<<1) | (aval&1)) & 3);
  return vhpiEnumTLookup[idx];
}

static int uvm_hdl_set_vhdl(char* path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  int size, chunks, bit, i, j, aval, bval;
  vhpiValueT value_s;
  vhpiHandleT r = vhpi_handle_by_name(path, 0);

  if(maxsize == -1) maxsize = uvm_hdl_max_width();
  if(maxsize == -1) maxsize = 1024;

  size = vhpi_get(vhpiSizeP, r);
  if(size > maxsize)
    {
      m_uvm_error("UVM/DPI/VHDL_SET","hdl path %s is %0d bits, but the current maximum size is %0d. You may redefine it using the compile-time flag: -define UVM_HDL_MAX_WIDTH=<value>", path, size,maxsize);

      tf_dofinish();
    }
  chunks = (size-1)/32 + 1;

  value_s.format = vhpiObjTypeVal;
  value_s.bufSize = 0;
  value_s.value.str = NULL;

  vhpi_get_value(r, &value_s);

  switch(value_s.format)
    {
    case vhpiEnumVal:
      {
	value_s.value.enumv = vhpi2val(value[0].aval,value[0].bval);
	break;
      }
    case vhpiEnumVecVal:
      {
	value_s.bufSize = size*sizeof(int); 
	value_s.value.enumvs = (vhpiEnumT *)malloc(size*sizeof(int));

	vhpi_get_value(r, &value_s);
	chunks = (size-1)/32 + 1;

	bit = 0;
	for(i=0;i<chunks && bit<size; ++i)
	  {
	    aval = value[i].aval;
	    bval = value[i].bval;

	    for(j=0;j<32 && bit<size; ++j)
	      {
		value_s.value.enumvs[size-bit-1]= vhpi2val(aval,bval);
		aval>>=1; bval>>=1;
		bit++;
	      }
	  }
	break;
      }
    default:
      {
	m_uvm_error("UVM/DPI/VHDL_SET","Failed to set value to hdl path %s (unexpected type: %0d)", path, value_s.format);
	tf_dofinish();
	return 0;
      }
    }

  vhpi_put_value(r, &value_s, flag);  

  if(value_s.format == vhpiEnumVecVal)
    {
      free(value_s.value.enumvs);
    }
  return 1;
}

/*
 * Given a path, look the path name up using the PLI
 * and return its 'value'.
 */
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  int i, size, chunks;
  vpiHandle r;
  s_vpi_value value_s;

  r = vpi_handle_by_name(path, 0);

  if(r == 0)
    {
      m_uvm_error("UVM/DPI/VLOG_GET","unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name",path);
      // Exiting is too harsh. Just return instead.
      // tf_dofinish();
      return 0;
    }
  else
    {
      if(maxsize == -1) 
        maxsize = uvm_hdl_max_width();

      size = vpi_get(vpiSize, r);
      if(size > maxsize)
	{
	  m_uvm_error("UVM/DPI/VLOG_GET","hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>",
		  path,size,maxsize);
	  //tf_dofinish();

	  vpi_release_handle(r);

	  return 0;
	}
      chunks = (size-1)/32 + 1;

      value_s.format = vpiVectorVal;
      vpi_get_value(r, &value_s);
      /*dpi and vpi are reversed*/
      for(i=0;i<chunks; ++i)
	{
	  value[i].aval = value_s.value.vector[i].aval;
	  value[i].bval = value_s.value.vector[i].bval;
	}
    }
  //vpi_printf("uvm_hdl_get_vlog(%s,%0x)\n",path,value[0].aval);

  vpi_release_handle(r);

  return 1;
}

static int uvm_hdl_get_vhdl(char* path, p_vpi_vecval value)
{
  static int maxsize = -1;
  int i, j, size, chunks, bit, aval, bval, rtn;
  vhpiValueT value_s;
  vhpiHandleT r = vhpi_handle_by_name(path, 0);

  if(maxsize == -1) maxsize = uvm_hdl_max_width();
  if(maxsize == -1) maxsize = 1024;

  size = vhpi_get(vhpiSizeP, r);
  if(size > maxsize)
    {
	  m_uvm_error("UVM/DPI/HDL_SET","hdl path %s is %0d bits, but the maximum size is %0d, redefine using -define UVM_HDL_MAX_WIDTH=<value>", path, size,maxsize);
      tf_dofinish();
    }
  chunks = (size-1)/32 + 1;
  value_s.format = vhpiObjTypeVal;
  value_s.bufSize = 0;
  value_s.value.str = NULL;

  rtn = vhpi_get_value(r, &value_s);

  if(vhpi_check_error(0) != 0) 
    {
	  m_uvm_error("UVM/DPI/VHDL_GET","Failed to get value from hdl path %s",path);
      tf_dofinish();
      return 0;
    }

  switch (value_s.format)
    {
    case vhpiIntVal:
      {
	value[0].aval = value_s.value.intg;
	value[0].bval = 0;
	break;
      }
    case vhpiEnumVal:
      {
	switch(value_s.value.enumv)
	  {
	  case vhpiU: 
	  case vhpiW: 
	  case vhpiX: 
	    {
	      value[0].aval = 1; value[0].bval = 1; break;
	    }
	  case vhpiZ: 
	    {
	      value[0].aval = 0; value[0].bval = 1; break;
	    }
	  case vhpi0: 
	  case vhpiL: 
	  case vhpiDontCare: 
	    {
	      value[0].aval = 0; value[0].bval = 0; break;
	    }
	  case vhpi1: 
	  case vhpiH: 
	    {
	      value[0].aval = 1; value[0].bval = 0; break;
	    }
	  }
	break;
      }
    case vhpiEnumVecVal:
      {
	value_s.bufSize = size;
	value_s.value.str = (char*)malloc(size);
	rtn = vhpi_get_value(r, &value_s);
	if (rtn > 0) {
	  value_s.value.str = (char*)realloc(value_s.value.str, rtn);
	  value_s.bufSize = rtn;
	  vhpi_get_value(r, &value_s);
	}
	for(i=0; i<((maxsize-1)/32+1); ++i)
	  {
	    value[i].aval = 0;
	    value[i].bval = 0;
	  }
	bit = 0;
	for(i=0;i<chunks && bit<size; ++i)
	  {
	    aval = 0;
	    bval = 0;
	    for(j=0;(j<32) && (bit<size); ++j)
	      {
		aval<<=1; bval<<=1;
		switch(value_s.value.enumvs[bit])
		  {
		  case vhpiU: 
		  case vhpiW: 
		  case vhpiX: 
		    {
		      aval |= 1;
		      bval |= 1;
		      break;
		    }
		  case vhpiZ: 
		    {
		      bval |= 1;
		      break;
		    }
		  case vhpi0: 
		  case vhpiL: 
		  case vhpiDontCare: 
		    {
		      break;
		    }
		  case vhpi1: 
		  case vhpiH: 
		    {
		      aval |= 1;
		      break;
		    }
		  }
		bit++;
	      }
	    value[i].aval = aval;
	    value[i].bval = bval;
	    free (value_s.value.str);
	  }
	break;
      }
    default:
      {
    	  m_uvm_error("UVM/DPI/VHDL_GET","Failed to get value from hdl path %s (unexpected type: %0d)", path, value_s.format);

	tf_dofinish();
	return 0;
      }
    }
  return 1;
}

/*
 * Given a path, look the path name up using the PLI,
 * but don't set or get. Just check.
 *
 * Return 0 if NOT found.
 * Return 1 if found.
 */
int uvm_hdl_check_path(char *path)
{
  vhpiHandleT handle;
  int language;

  m_uvm_get_object_handle(path,&handle,&language);

  return (handle!=0);
}

static void m_uvm_error(const char *id, const char *msg, ...) {
		va_list argptr;
		va_start(argptr,msg);
		vsprintf(m_uvm_temp_print_buffer,msg, argptr);
		va_end(argptr);
	    m_uvm_report_dpi(M_UVM_ERROR,
			 (char *) id,
			 &m_uvm_temp_print_buffer[0],
			 M_UVM_NONE,
			 (char*) __FILE__,
			 __LINE__);
}
/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and return its 'value'.
 */
int uvm_hdl_read(char *path, p_vpi_vecval value)
{
		vhpiHandleT handle;
		int language;

		if(is_valid_path_slice(path)) {
			clear_value(value);
			return uvm_hdl_get_vlog_partsel(path, value, vpiNoDelay);
		}

		m_uvm_get_object_handle(path,&handle,&language);
		switch(language) {
			case vhpiVerilog:  return uvm_hdl_get_vlog(path, value, vpiNoDelay);
			case vhpiVHDL: return uvm_hdl_get_vhdl(path, value);
			default:m_uvm_error("UVM/DPI/NOBJ1","name %s cannot be resolved to a hdl object (vlog,vhdl,vlog-slice)",path); return 0;
		}
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_deposit(char *path, p_vpi_vecval value)
{
	vhpiHandleT handle;
	int language;

	if(is_valid_path_slice(path))
		return uvm_hdl_set_vlog_partsel(path, value, vpiNoDelay);

	m_uvm_get_object_handle(path,&handle,&language);
	switch(language) {
		case vhpiVerilog:  return uvm_hdl_set_vlog(path, value, vpiNoDelay);
		case vhpiVHDL: return uvm_hdl_set_vhdl(path, value, vhpiDepositPropagate);
		default:m_uvm_error("UVM/DPI/NOBJ2","name %s cannot be resolved to a hdl object (vlog,vhdl,vlog-slice)",path); return 0;
	}
}


/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_force(char *path, p_vpi_vecval value)
{
	vhpiHandleT handle;
	int language;

	if(is_valid_path_slice(path))
		return uvm_hdl_set_vlog_partsel(path, value, vpiForceFlag);

	m_uvm_get_object_handle(path,&handle,&language);
	switch(language) {
		case vhpiVerilog:  return uvm_hdl_set_vlog(path, value, vpiForceFlag);
		case vhpiVHDL: return uvm_hdl_set_vhdl(path, value, vhpiForcePropagate);
		default:m_uvm_error("UVM/DPI/NOBJ3","name %s cannot be resolved to a hdl object (vlog,vhdl,vlog-slice)",path); return 0;
	}
}


/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release_and_read(char *path, p_vpi_vecval value)
{
	vhpiHandleT handle;
	int language;

	if(is_valid_path_slice(path)) {
		uvm_hdl_set_vlog_partsel(path, value, vpiReleaseFlag);
		clear_value(value);
		return uvm_hdl_get_vlog_partsel(path, value, vpiNoDelay);
	}

	m_uvm_get_object_handle(path,&handle,&language);
	switch(language) {
		case vhpiVerilog:      uvm_hdl_set_vlog(path, value, vpiReleaseFlag); return uvm_hdl_get_vlog(path, value, vpiNoDelay);
		case vhpiVHDL:    uvm_hdl_set_vhdl(path, value, vhpiReleaseKV); return uvm_hdl_get_vhdl(path, value);
		default:m_uvm_error("UVM/DPI/NOBJ4","name %s cannot be resolved to a hdl object (vlog,vhdl,vlog-slice)",path); return 0;
	}
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release(char *path)
{
	s_vpi_vecval value;
	vhpiHandleT handle;
	int language;

	if(is_valid_path_slice(path))
		return uvm_hdl_set_vlog_partsel(path, &value, vpiReleaseFlag);

	m_uvm_get_object_handle(path,&handle,&language);
	switch(language) {
		case vhpiVerilog:  return uvm_hdl_set_vlog(path, &value, vpiReleaseFlag);
		case vhpiVHDL: return uvm_hdl_set_vhdl(path, &value, vhpiReleaseKV);
		default:m_uvm_error("UVM/DPI/NOBJ5","name %s cannot be resolved to a hdl object (vlog,vhdl,vlog-slice)",path); return 0;
	}
}
