//----------------------------------------------------------------------
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2023 Marvell International Ltd.
// Copyright 2009-2011 Mentor Graphics Corporation
// Copyright 2013-2024 NVIDIA Corporation
// Copyright 2010-2022 Synopsys, Inc.
//
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


#include "uvm_dpi.h"
#include <math.h>

#include "sv_vpi_user.h"
#include "svdpi.h"
#include "vcsuser.h"

#ifdef VCSMX
#include "mhpi_user.h"
#include "vhpi_user.h"
#endif

#ifndef VCSMX_DO_NOT_ERROR_ON_NULL_HANDLE
#define VCSMX_ERROR_ON_NULL_HANDLE
#endif

#if defined(VCSMX_FAST_UVM) && !defined(MHPI_FAST_UVM)
#error "UVM_ERROR: THIS VERSION OF VCS DOESN'T SUPPORT VCSMX_FAST_UVM. Compile without -DVCSMX_FAST_UVM"
#endif

/*
 * Functionn to check if target variable is compatible with vector
 */
/* 
 * This code ceccks if the given handle is not of type Array or unpacked
 * struct
 */ 

static int vector_compat_type(vpiHandle obj)
{
    int vector_compatible = 1;
    switch(vpi_get(vpiType, obj)) {
      case vpiArrayVar:
      case vpiArrayNet:
        vector_compatible = 0;
        break;
      case vpiStructVar:
      case vpiUnionVar:
        if (vpi_get(vpiVector, obj) == 0) {
            vector_compatible = 0;
        }
        break;
    }
    if (!vector_compatible) {
        return 0;
    }
    return 1;
}


#define UVM_DPI_DO_TYPE_CHECK

#ifdef UVM_DPI_DISABLE_DO_TYPE_CHECK
#undef UVM_DPI_DO_TYPE_CHECK
#endif

#ifdef UVM_DPI_DO_TYPE_CHECK
   static int (*check_type)(vpiHandle) = &vector_compat_type;
#else
   static int vector_compat_type_stub(vpiHandle obj)
   {
       return 1;
   }
   static int (*check_type)(vpiHandle) = &vector_compat_type_stub;
#endif

/* 
 * UVM HDL access C code.
 *
 */

#ifdef VCSMX_FAST_UVM
static char* get_memory_for_alloc(int need)
{
    static int alloc_size = 0;
    static char* alloc = NULL;
    if (need > alloc_size) {
        if (alloc_size == 0) alloc_size = need;
        while (alloc_size < need) alloc_size *= 2;
        alloc = (char*)realloc(alloc, alloc_size);
    }
    return alloc;
}
#endif
/*
 * This C code checks to see if there is PLI handle
 * with a value set to define the maximum bit width.
 *
 * If no such variable is found, then the default 
 * width of 1024 is used.
 *
 * This function should only get called once or twice,
 * its return value is cached in the caller.
 *
 */
static int uvm_hdl_max_width()
{
  vpiHandle ms;
  s_vpi_value value_s = { vpiIntVal, { 0 } };
  ms = vpi_handle_by_name((PLI_BYTE8*) "uvm_pkg::UVM_HDL_MAX_WIDTH", 0);
  if(ms == 0) 
    return 1024;  /* If nothing else is defined, 
                     this is the DEFAULT */
  vpi_get_value(ms, &value_s);
  return value_s.value.integer;
}


/*
 * Given a path, look the path name up using the PLI,
 * and set it to 'value'.
 */
#ifdef VCSMX_FAST_UVM
static int uvm_hdl_set_vlog(vpiHandle r, char* path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  s_vpi_value value_s = { vpiIntVal, { 0 } };
  s_vpi_time  time_s = { vpiSimTime, 0, 0, 0.0 };

  if(r == 0)
  {
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_SET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
    return 0;
  }
  else
  {
    if(maxsize == -1)
        maxsize = uvm_hdl_max_width();

    if (flag == vpiReleaseFlag) {
      //size = vpi_get(vpiSize, r);
      //value_p = (p_vpi_vecval)(malloc(((size-1)/32+1)*8*sizeof(s_vpi_vecval)));
      //value = &value_p;
    }
    value_s.format = vpiVectorVal;
    value_s.value.vector = value;
    if (!check_type(r)) {
        const char * err_str = "Object pointed to by path  (%s) is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    vpi_put_value(r, &value_s, &time_s, flag);
    if (vpi_chk_error(NULL)) {
        const char * err_str = "set: unable to write to hdl path (%s)\n  or You may not have PLI/ACC visibility to that name";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    if (value == NULL) {
      value = value_s.value.vector;
    }
  }
  return 1;
}
#else
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  vpiHandle r;
  s_vpi_value value_s = { vpiIntVal, { 0 } };
  s_vpi_time  time_s = { vpiSimTime, 0, 0, 0.0 };

#ifdef VCSMX
#ifndef USE_DOT_AS_HIER_SEP
  mhpi_initialize('/');
#else
  mhpi_initialize('.');
#endif
  mhpiHandleT h = mhpi_handle_by_name(path, 0);
  r = (vpiHandle) mhpi_get_vpi_handle(h);
  mhpi_release_parent_handle(h);
#else
  r = vpi_handle_by_name(path, 0);
#endif

  if(r == 0)
  {
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_SET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
    return 0;
  }
  else
  {
        if(maxsize == -1) 
        maxsize = uvm_hdl_max_width();

    if (flag == vpiReleaseFlag) {
      //size = vpi_get(vpiSize, r);
      //value_p = (p_vpi_vecval)(malloc(((size-1)/32+1)*8*sizeof(s_vpi_vecval)));
      //value = &value_p;
    }
    value_s.format = vpiVectorVal;
    value_s.value.vector = value;
    if (!check_type(r)) {
        const char * err_str = "set:Object pointed to by path '%s' is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value.";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    vpi_put_value(r, &value_s, &time_s, flag);  
    if (vpi_chk_error(NULL)) {

        const char * err_str = "Unable to write to hdl path (%s)\n, You may not have sufficient PLI/ACC capabilites enabled for that path\n";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    if (value == NULL) {
      value = value_s.value.vector;
    }
  }
  return 1;
}
#endif


/*
 * Given a path, look the path name up using the PLI
 * and return its 'value'.
 */
#ifdef VCSMX_FAST_UVM
static int uvm_hdl_get_vlog(vpiHandle r, char* path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  int i, size, chunks;
  s_vpi_value value_s;


  if(r == 0)
  {
      const char * err_str = "get: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
              (char*)"UVM/DPI/HDL_GET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
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
      const char * err_str = "uvm_reg : hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>";
      char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
      sprintf(buffer, err_str, path, size, maxsize);
      m_uvm_report_dpi(M_UVM_ERROR,
              (char*)"UVM/DPI/HDL_SET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
      vpi_release_handle(r);
      return 0;
    }
  #ifdef PREFILL_ALL_BITS_WITH_ZERO
    chunks = (maxsize-1)/32 + 1;
    for(i=0;i<chunks; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
  #endif
    chunks = (size-1)/32 + 1;

    value_s.format = vpiVectorVal;
    if (!check_type(r)) {
        const char * err_str = " Object pointed to by path '%s' is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value.";
        char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
        sprintf(buffer, err_str, path, size, maxsize);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*)"UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,
                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    vpi_get_value(r, &value_s);
    if (vpi_chk_error(NULL)) {
        const char * err_str = "set: : unable to perform read on hdl path (%s)\n You may not have sufficient PLI/ACC capabilites enabled for that path\n";
        char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
        sprintf(buffer, err_str, path, size, maxsize);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*)"UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,
                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    /*dpi and vpi are reversed*/
    for(i=0;i<chunks; ++i)
    {
      value[i].aval = value_s.value.vector[i].aval;
      value[i].bval = value_s.value.vector[i].bval;
    }
  }
  return 1;
}
#else
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag)
{
  static int maxsize = -1;
  int i, size, chunks;
  vpiHandle r;
  s_vpi_value value_s;

#ifdef VCSMX
  mhpiHandleT h = mhpi_handle_by_name(path, 0);
  r = (vpiHandle) mhpi_get_vpi_handle(h);
  mhpi_release_parent_handle(h);
#else
  r = vpi_handle_by_name(path, 0);
#endif

  if(r == 0)
  {
      const char * err_str = "get: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
              (char*)"UVM/DPI/HDL_GET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
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
      const char * err_str = "uvm_reg : hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>";
      char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
      sprintf(buffer, err_str, path, size, maxsize);
      m_uvm_report_dpi(M_UVM_ERROR,
              (char*)"UVM/DPI/HDL_SET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
      vpi_release_handle(r);
      return 0;
    }
  #ifdef PREFILL_ALL_BITS_WITH_ZERO
    chunks = (maxsize-1)/32 + 1;
    for(i=0;i<chunks; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
  #endif
    chunks = (size-1)/32 + 1;

    value_s.format = vpiVectorVal;
    if (!check_type(r)) {
        const char * err_str = "Object pointed to by path '%s' is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value.";
        char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
        sprintf(buffer, err_str, path, size, maxsize);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*)"UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,
                __LINE__);
        vpi_release_handle(r);
        return 0;
    }
    vpi_get_value(r, &value_s);
    if (vpi_chk_error(NULL)) {
        const char * err_str = "set: unable to perform read on hdl path (%s)\n. You may not have sufficient PLI/ACC capabilites enabled for that path\n";
        char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
        sprintf(buffer, err_str, path, size, maxsize);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*)"UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,
                __LINE__);
//        vpi_printf((PLI_BYTE8*) "UVM_ERROR: set: unable to perform read on hdl path (%s)\n",path);
  //      vpi_printf((PLI_BYTE8*) "You may not have sufficient PLI/ACC capabilites enabled for that path\n");
        vpi_release_handle(r);
        return 0;
    }
    /*dpi and vpi are reversed*/
    for(i=0;i<chunks; ++i)
    {
        value[i].aval = value_s.value.vector[i].aval;
      value[i].bval = value_s.value.vector[i].bval;
    }
  }
  //vpi_printf("uvm_hdl_get_vlog(%s,%0x)\n",path,value[0].aval);
  return 1;
}
#endif

#ifdef VCSMX_FAST_UVM
static int uvm_hdl_get_vhpi(vhpiHandleT r, char* path, /*vhpiEnumT *value*/ p_vpi_vecval value)
{
  static int maxsize = -1;
  int size, chunks, i, j, rtn , bit, aval, bval;
  vhpiValueT value_s;

  if (r == 0) {
    const char * err_str = "get: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
    char buffer[strlen(err_str) + strlen(path)];
    sprintf(buffer, err_str, path);
    m_uvm_report_dpi(M_UVM_ERROR, (char*)"UVM/DPI/HDL_GET", &buffer[0], M_UVM_NONE, (char*)__FILE__, __LINE__);
    return 0;  
  }
  else {
    if (maxsize == -1) {
      maxsize = uvm_hdl_max_width();
    }

    size = vhpi_get(vhpiSizeP, r);
    if (size > maxsize) {
      const char * err_str = "uvm_reg : hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>";
      char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
      sprintf(buffer, err_str, path, size, maxsize);
      m_uvm_report_dpi(M_UVM_ERROR, (char*)"UVM/DPI/VHDL_GET", &buffer[0], M_UVM_NONE, (char*)__FILE__, __LINE__);
      return 0;
    }

    // start to convert to p_vpi_vecval
    memset(value, 0, (maxsize-1)/32+1); 
    vhpiHandleT baseTypeH = vhpi_handle (vhpiBaseType, r);
    char *typeName = vhpi_get_str (vhpiNameP, baseTypeH);
    if ((vhpi_get(vhpiIsScalarP, r)) == 1) {
      if (!strcmp(typeName, "INTEGER")) {
        value_s.format =  vhpiIntVal;
        rtn = vhpi_get_value(r, &value_s);
        value[0].aval = value_s.value.intg;
        value[0].bval = 0;
        return 1;
      }
    }
    chunks = (size - 1)/ 32 + 1;
    value_s.format = vhpiEnumVecVal;
    value_s.bufSize = size;
    value_s.value.str = get_memory_for_alloc(size);
    rtn = vhpi_get_value(r, &value_s);
    if (rtn > 0) {
      value_s.value.str = get_memory_for_alloc(rtn);
      value_s.bufSize = rtn; 
      vhpi_get_value(r, &value_s); 
    }

    // start to convert to p_vpi_vecval
    memset(value, 0, (maxsize-1)/32+1); 
    bit = 0;
    for (i = 0; i < chunks && bit < size; ++i) {
      aval = 0;
      bval = 0;
      for(j=0;(j<32) && (bit<size); ++j)
      {
        aval<<=1; bval<<=1;
        switch(value_s.value.enums[bit])
        {
          case 0:
          case 5:
          case 1:
          {
            aval |= 1;
            bval |= 1;
            break;
          }
          case 4:
          {
            bval |= 1;
            break;
          }
          case 2:
          case 6:
          case 8:
          {
            break;
          }
          case 3:
          case 7:
          {
            aval |= 1;
            break;
          }
        }
        bit++;
      }
      value[i].aval = aval;
      value[i].bval = bval;
    }
  }
  return 1;
}

int uvm_memory_load(const char* nid,
                     const char* scope,
                     const char* fileName,
                     const char* radix,
                     const char* startaddr,
                     const char* endaddr,
                     const char* type)
{
    mhpi_uvm_ucli_memory_load(nid, scope, fileName, radix,
                          startaddr, endaddr, type);
    return 1;
}
#else
int uvm_memory_load(const char* nid,
                     const char* scope,
                     const char* fileName,
                     const char* radix,
                     const char* startaddr,
                     const char* endaddr,
                     const char* type)
{
    //TODO:: furture implementation for pure verilog
    m_uvm_report_dpi(M_UVM_ERROR,
            (char*) "UVM/DPI/MEMORY",
            (char*) "uvm_memory_load: uvm_memory_load is not supported, please compile with -DVCSMX_FAST_UVM",
            M_UVM_NONE,
            (char*)__FILE__,
            __LINE__);


//    vpi_printf((PLI_BYTE8*) "UVM_ERROR: uvm_memory_load is not supported, please compile with -DVCSMX_FAST_UVM\n");
    return 0;
}
#endif
/*
 * Given a path, look the path name up using the PLI,
 * but don't set or get. Just check.
 *
 * Return 0 if NOT found.
 * Return 1 if found.
 */
int uvm_hdl_check_path(char *path)
{
#ifndef VCSMX
  vpiHandle r;

  r = vpi_handle_by_name(path, 0);

  if(r == 0)
      return 0;
  else
    return 1;
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
   mhpiHandleT h = mhpi_uvm_handle_by_name(path, 0);
#else
   mhpiHandleT h = mhpi_handle_by_name(path, 0);
#endif
    if (h == 0)  {
      return 0;
    } else {
     mhpi_release_parent_handle(h);   
     return 1;
    }
#endif
}

/*
 * convert binary to integer
 */
unsigned long int uvm_hdl_btoi(char *binVal) {
  unsigned long int dec=0, j = 0;
  unsigned long long int bin;
  int i;
  char tmp[2];
  tmp[1] = '\0';

  for(i= strlen(binVal) -1 ; i >= 0 ; i--) {
    tmp[0] = binVal[i];
    bin = atoi(tmp);
    dec = dec+(bin*(pow(2,j)));
    j++;
  }
  return(dec);
}


/*
 *decimal to hex conversion
 */
char *uvm_hdl_dtob(unsigned long int decimalNumber, unsigned long int msb) {
  unsigned int quotient;
  int  i=0,j, length;
  int binN[65];
  static char binaryNumber[65];
  memset(binN, 0, 65*sizeof(int));

  quotient = decimalNumber;


  do {
    binN[i++] = quotient%2;
    quotient = quotient/2;
  } while (quotient!=0);
  if (!msb)
    length = 32;
  else
    length = i;

  for (i=length-1, j = 0; i>=0; i--) {
    binaryNumber[j++] = binN[i]?'1':'0';
  }
  binaryNumber[j] = '\0';
  return(binaryNumber);
}


/*
 * Mixed lanaguage API Get calls
 */
#ifdef VCSMX
#ifdef VCSMX_FAST_UVM
int uvm_hdl_get_mhdl(vhpiHandleT vhpiH, char *path, p_vpi_vecval value) {

  long int value_int;
  static int maxsize = -1;


  char *binVal;
  int i = 0;
  vhpiValueT value1;
  p_vpi_vecval vecval;
  int size = 0;
  int chunks;
/*
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
  mhpiHandleT mhpiH = mhpi_uvm_handle_by_name(path, 0);
  vhpiHandleT vhpiH = (long unsigned int *)mhpi_get_vhpi_handle(mhpiH);*/
  value1.format=vhpiStrVal;
  size = vhpi_get(vhpiSizeP, vhpiH);

  if (maxsize == -1)
      maxsize = uvm_hdl_max_width();

  if(size > maxsize)
  {
    const char * err_str = "uvm_reg : hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>";
    char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
    sprintf(buffer, err_str, path, size, maxsize);
    m_uvm_report_dpi(M_UVM_ERROR,
  		  (char*)"UVM/DPI/HDL_SET",
                     &buffer[0],
                     M_UVM_NONE,
                     (char*)__FILE__,
                     __LINE__);
    return 0;
  }
  #ifdef PREFILL_ALL_BITS_WITH_ZERO
    chunks = (maxsize-1)/32 + 1;
    for(i=0;i<chunks; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
  #endif

  value1.bufSize = size+1;
  value1.value.str = get_memory_for_alloc(size + 1);
  if (vhpi_get_value(vhpiH, &value1) == 0) {
    int max_i = (size -1)/32 + 1;
    char sub_value[33];
    binVal = value1.value.str;
    for (int i = 0; i < max_i; i++) {
        int bits_to_consider = 32;

        if (i == 0) {
            bits_to_consider = size  - (max_i-1)*32;
        }

        strncpy(sub_value, binVal, bits_to_consider);
        sub_value[bits_to_consider]= '\0';

        for (int j = 0; j < bits_to_consider; j++) {
            switch(sub_value[j]) {
              case '0':
                value[max_i-i-1].aval = value[max_i-i-1].aval << 1;
                value[max_i-i-1].bval = value[max_i-i-1].bval << 1;
                break;
              case '1':
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = value[max_i-i-1].bval << 1;
                break;
              case 'U':
              case 'X':
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
                break;
              case 'Z':
                value[max_i-i-1].aval = value[max_i-i-1].aval << 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
                break;
              default:
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
            }
        }
        binVal = binVal+bits_to_consider;
    }

    return(1);
    

  } else {
    return (0);
  }

}
#else
int uvm_hdl_get_mhdl(char *path, p_vpi_vecval value) {

  long int value_int;
  static int maxsize = -1;


  char *binVal;
  int i = 0;
  vhpiValueT value1;
  p_vpi_vecval vecval;
  int size = 0;
  int chunks;

#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
  mhpiHandleT mhpiH = mhpi_handle_by_name(path, 0);
  vhpiHandleT vhpiH = (long unsigned int *)mhpi_get_vhpi_handle(mhpiH);
  value1.format=vhpiStrVal;
  size = vhpi_get(vhpiSizeP, vhpiH);

  if (maxsize == -1)
      maxsize = uvm_hdl_max_width();

  if(size > maxsize)
  {
    const char * err_str = "uvm_reg : hdl path '%s' is %0d bits, but the maximum size is %0d.  You can increase the maximum via a compile-time flag: +define+UVM_HDL_MAX_WIDTH=<value>";
    char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
    sprintf(buffer, err_str, path, size, maxsize);
    m_uvm_report_dpi(M_UVM_ERROR,
          (char*)"UVM/DPI/HDL_SET",
                     &buffer[0],
                     M_UVM_NONE,
                     (char*)__FILE__,
                     __LINE__);
    return 0;
  }
  #ifdef PREFILL_ALL_BITS_WITH_ZERO
    chunks = (maxsize-1)/32 + 1;
    for(i=0;i<chunks; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
  #endif

  //value1.bufSize = (size)/8 + 1;
  value1.bufSize = size+1;
  value1.value.str = (char*)malloc(value1.bufSize*sizeof(char));

  if (vhpi_get_value(vhpiH, &value1) == 0) {
    int max_i = (size -1)/32 + 1;
    char sub_value[33];
    binVal = value1.value.str;
    for (int i = 0; i < max_i; i++) {
        int bits_to_consider = 32;

        if (i == 0) {
            bits_to_consider = size  - (max_i-1)*32;
        }

        strncpy(sub_value, binVal, bits_to_consider);
        sub_value[bits_to_consider]= '\0';

        for (int j = 0; j < bits_to_consider; j++) {
            switch(sub_value[j]) {
              case '0':
                value[max_i-i-1].aval = value[max_i-i-1].aval << 1;
                value[max_i-i-1].bval = value[max_i-i-1].bval << 1;
                break;
              case '1':
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = value[max_i-i-1].bval << 1;
                break;
              case 'U':
              case 'X':
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
                break;
              case 'Z':
                value[max_i-i-1].aval = value[max_i-i-1].aval << 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
                break;
              default:
                value[max_i-i-1].aval = (value[max_i-i-1].aval << 1) + 1;
                value[max_i-i-1].bval = (value[max_i-i-1].bval << 1) + 1;
            }
        }
        binVal = binVal+ bits_to_consider;
    }
    mhpi_release_parent_handle(mhpiH);

    free(value1.value.str);
    return(1);

  } else {
    mhpi_release_parent_handle(mhpiH);
    free(value1.value.str);
    return (0);
  }

}
#endif
#endif

#ifdef VCSMX_FAST_UVM
char* uvm_hdl_read_string(char* path)
{
#ifdef VCSMX
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
    mhpiHandleT mhpiH = mhpi_uvm_handle_by_name(path, 0);
    if (mhpi_get(mhpiPliP, mhpiH) == mhpiVhpiPli) {
       vhpiValueT getValue;
       char* valueStr = (char*)0;
       vhpiIntT strValueSize = 0;
       vhpiHandleT h = (vhpiHandleT)mhpi_get_vhpi_handle(mhpiH);
       mhpi_release_parent_handle(mhpiH);
       if (h) {
           strValueSize = vhpi_value_size(h, vhpiStrVal);
           if (strValueSize) {
               getValue.value.str = get_memory_for_alloc( 8*strValueSize+1);
           } else {
               return valueStr;
           }

           getValue.format = vhpiStrVal;
           getValue.bufSize = strValueSize;
           if (!vhpi_get_value(h, &getValue)) {
               valueStr = getValue.value.str;
               getValue.value.str = (char*)0;
           }
           vhpi_release_handle(h);
       }
       return valueStr;
    } else if (mhpi_get(mhpiPliP, mhpiH) == mhpiVpiPli){
       vpiHandle h = (vpiHandle)mhpi_get_vpi_handle(mhpiH);
       mhpi_release_parent_handle(mhpiH);

       if (h) {
           s_vpi_value getValue;
           getValue.format = vpiStringVal;
           if (!check_type(h)) {
               const char * err_str = " Object pointed to by path '%s' is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value.";
               char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
               sprintf(buffer, err_str, path, size, maxsize);
               m_uvm_report_dpi(M_UVM_ERROR,
                       (char*)"UVM/DPI/HDL_SET",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
               return 0;
           }
           vpi_get_value(h, &getValue);
           vpi_release_handle(h);
           return getValue.value.str;
       }
       return (char*)0;
    }
#else
    vpiHandle h = vpi_handle_by_name(path, 0);
    if (h) {
        s_vpi_value getValue;
        getValue.format = vpiStringVal;
        if (!check_type(h)) {
            const char * err_str = " Object pointed to by path '%s' is not of supported type\n (Unpacked Array/Struct/Union type) for reading/writing value.";
            char buffer[strlen(err_str) + strlen(path) + (2*int_str_max(10))];
            sprintf(buffer, err_str, path, size, maxsize);
            m_uvm_report_dpi(M_UVM_ERROR,
                    (char*)"UVM/DPI/HDL_SET",
                    &buffer[0],
                    M_UVM_NONE,
                    (char*)__FILE__,
                    __LINE__);
            return 0;
        }
        vpi_get_value(h, &getValue);
        vpi_release_handle(h);
        return getValue.value.str;
    }
    return (char*)0;
#endif
}
#else 
char* uvm_hdl_read_string(char* path)
{
    m_uvm_report_dpi(M_UVM_ERROR,
            (char*) "UVM/DPI/REGEX_ALLOC",
            (char*) "uvm_hdl_read_string: uvm_hdl_read_string is not supported, please compile with -DVCSMX_FAST_UVM",
            M_UVM_NONE,
            (char*)__FILE__,
            __LINE__);
    return (char*)0;
}
#endif
/*
 * Given a path, look the path name up using the PLI
 * or the VHPI, and return its 'value'.
 */

int uvm_hdl_read(char *path, p_vpi_vecval value)
{
#ifndef VCSMX
#ifdef VCSMX_FAST_UVM
    r = vpi_handle_by_name(path, 0);
    int res = uvm_hdl_get_vlog(r, path, value, vpiNoDelay);
    vpi_release_handle(r);
    return res;
#else
    return uvm_hdl_get_vlog(path, value, vpiNoDelay);
#endif
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
    mhpiHandleT h = mhpi_uvm_handle_by_name(path, 0);
    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
      vpiHandle r = (vpiHandle) mhpi_get_vpi_handle(h);
      int res = uvm_hdl_get_vlog(r, path, value, vpiNoDelay);
      mhpi_release_handle(h);
      return res;
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
        vhpiHandleT r = (vhpiHandleT) mhpi_get_vhpi_handle(h);
        int res = uvm_hdl_get_vhpi(r, path, value);
        mhpi_release_handle(h);
        return res;
    }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
        const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
#endif        
        return 0;
    }
#else
    mhpiHandleT h = mhpi_handle_by_name(path, 0);
    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
    mhpi_release_parent_handle(h);
      return uvm_hdl_get_vlog(path, value, vpiNoDelay);
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {

    mhpi_release_parent_handle(h);
      return uvm_hdl_get_mhdl(path,value);
    }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
        const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
        char buffer[strlen(err_str) + strlen(path)];
        sprintf(buffer, err_str, path);
        m_uvm_report_dpi(M_UVM_ERROR,
                (char*) "UVM/DPI/HDL_SET",
                &buffer[0],
                M_UVM_NONE,
                (char*)__FILE__,

                __LINE__);
#endif
        return 0;
    }

#endif
#endif

}


/*
 * Mixed Language API Set calls
 */
#ifdef VCSMX
#ifdef VCSMX_FAST_UVM
int uvm_hdl_set_mhdl(mhpiHandleT h, char *path, p_vpi_vecval value, mhpiPutValueFlagsT flags) 
{
    mhpiRealT forceDelay = 0;
    mhpiRealT cancelDelay = -1;
    mhpiReturnT ret;
    mhpiHandleT mhpi_mhRegion = mhpi_handle(mhpiScope, h);

    PLI_UINT32 size = mhpi_get(mhpiSizeP, h);
    PLI_UINT32 max_i = (size-1)/32 + 1;
    char* buf = get_memory_for_alloc(size + 1);
    buf[0] = '\0';

    for (int i = max_i -1; i >= 0; i--) {
      int sz;  
      char* force_value =uvm_hdl_dtob(value[i].aval, ((max_i -1) ==i));
      sz = ((max_i - 1) == i) ? size - 32*(max_i-1) : 32;
      strncat(buf, force_value, sz);
    }

    ret = mhpi_force_value_by_handle(h, buf, flags, forceDelay, cancelDelay); 
    if (ret == mhpiRetOk) {
      return(1);
    }
    else 
      return(0);
}
#else
int uvm_hdl_set_mhdl(char *path, p_vpi_vecval value, mhpiPutValueFlagsT flags)
{
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
    mhpiRealT forceDelay = 0;
    mhpiRealT cancelDelay = -1;
    mhpiReturnT ret;
    mhpiHandleT h = mhpi_handle_by_name(path, 0);
    mhpiHandleT mhpi_mhRegion = mhpi_handle(mhpiScope, h);

    PLI_UINT32 size = mhpi_get(mhpiSizeP, h);
    PLI_UINT32 max_i = (size-1)/32 + 1;
    char* buf = (char *) malloc(sizeof(char)*(size+1));
    buf[0] = '\0';

    for (int i = max_i -1; i >= 0; i--) {
      int sz;
      char* force_value =uvm_hdl_dtob(value[i].aval, ((max_i -1) ==i));
      sz = ((max_i - 1) == i) ? size - 32*(max_i-1) : 32;
      strncat(buf, force_value, sz);
    }

    ret = mhpi_force_value(path, mhpi_mhRegion, buf, flags, forceDelay, cancelDelay);
    mhpi_release_parent_handle(h);
    if (ret == mhpiRetOk) {
      return(1);
    }
    else
      return(0);
}
#endif
#endif

/*
 * Given a path, look the path name up using the PLI
 * or the VHPI, and set it to 'value'.
 */
int uvm_hdl_deposit(char *path, p_vpi_vecval value)
{
#ifndef VCSMX
#ifdef VCSMX_FAST_UVM
    vpiHandle r = vpi_handle_by_name(path, 0);
    int res = uvm_hdl_set_vlog(r, path, value, vpiNoDelay);
    vpi_release_handle(r);
    return res;
#else
    return uvm_hdl_set_vlog(path, value, vpiNoDelay);
#endif
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
    mhpiHandleT h = mhpi_uvm_handle_by_name(path, 0);

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
      vpiHandle r = (vpiHandle) mhpi_get_vpi_handle(h);
      int res = uvm_hdl_set_vlog(r, path, value, vpiNoDelay);
      mhpi_release_handle(h);
      return res;
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
      int res = uvm_hdl_set_mhdl(h, path, value, mhpiNoDelay);
      return res;
    }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_DEPOSIT",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif      
      return (0);
    }  
#else
    mhpiHandleT h = mhpi_handle_by_name(path, 0);

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
    mhpi_release_parent_handle(h);
      return uvm_hdl_set_vlog(path, value, vpiNoDelay);
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
      mhpi_release_parent_handle(h);
      return uvm_hdl_set_mhdl(path, value, mhpiNoDelay);
     }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_DEPOSIT",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif      
      return (0);
    }
#endif
#endif
}


/*
 * Given a path, look the path name up using the PLI
 * or the VHPI, and set it to 'value'.
 */
int uvm_hdl_force(char *path, p_vpi_vecval value)
{
#ifndef VCSMX
#ifdef VCSMX_FAST_UVM
    vpiHandle r = vpi_handle_by_name(path, 0);
    int res = uvm_hdl_set_vlog(r, path, value, vpiForceFlag);
    vpi_release_handle(r); 
    return res;
#else
    return uvm_hdl_set_vlog(path, value, vpiForceFlag);
#endif
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
    mhpiHandleT h = mhpi_uvm_handle_by_name(path, 0);

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
      vpiHandle r = (vpiHandle) mhpi_get_vpi_handle(h);
      int res = uvm_hdl_set_vlog(r, path, value, vpiForceFlag);
      mhpi_release_handle(h);
      return res;
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
      int res = uvm_hdl_set_mhdl(h, path, value, mhpiForce);
      return res;
    }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_FORCE",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif      

      return (0);
    }
#else
    mhpiHandleT h = mhpi_handle_by_name(path, 0);

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
    mhpi_release_parent_handle(h);
      return uvm_hdl_set_vlog(path, value, vpiForceFlag);
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {

    mhpi_release_parent_handle(h);
      return uvm_hdl_set_mhdl(path, value, mhpiForce);

      }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_FORCE",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif      
      return (0);
    }
#endif
#endif
}


/*
 * Given a path, look the path name up using the PLI
 * or the VHPI, and release it.
 */
int uvm_hdl_release_and_read(char *path, p_vpi_vecval value)
{
#ifndef VCSMX
#ifdef VCSMX_FAST_UVM
    vpiHandle r = vpi_handle_by_name(path, 0);
    int res = uvm_hdl_set_vlog(r, path, value, vpiReleaseFlag);
    vpi_release_handle(r);
    return res;
#else
    return uvm_hdl_set_vlog(path, value, vpiReleaseFlag);
#endif
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
    mhpiHandleT mhpiH = mhpi_uvm_handle_by_name(path, 0);
#else
    mhpiHandleT mhpiH = mhpi_handle_by_name(path, 0);
#endif
    mhpiReturnT ret;
    mhpiHandleT mhpi_mhRegion = mhpi_handle(mhpiScope, mhpiH);
    if ((mhpi_get(mhpiPliP, mhpiH) ==  mhpiVpiPli) ||
	(mhpi_get(mhpiPliP, mhpiH) == mhpiVhpiPli)) {
      ret = mhpi_release_force(path, mhpi_mhRegion);
      mhpi_release_handle(mhpiH);
      if (ret == mhpiRetOk) {
        return(1);
      }
      else 
        return(0);
      }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_RELEASE_AND_READ",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif      
      return (0);
    }
#endif
}

/*
 * Given a path, look the path name up using the PLI
 * or the VHPI, and release it.
 */
int uvm_hdl_release(char *path)
{
    s_vpi_vecval value;
    p_vpi_vecval valuep = &value;
#ifndef VCSMX
#ifdef VCSMX_FAST_UVM
    vpiHandle r = vpi_handle_by_name(path, 0);
    int res = uvm_hdl_set_vlog(r, path, valuep, vpiReleaseFlag);
    vpi_release_handle(r);
    return res;
#else
    return uvm_hdl_set_vlog(path, valuep, vpiReleaseFlag);
#endif
#else
#ifndef USE_DOT_AS_HIER_SEP
    mhpi_initialize('/');
#else
    mhpi_initialize('.');
#endif
#ifdef VCSMX_FAST_UVM
    mhpiHandleT h = mhpi_uvm_handle_by_name(path, 0);
    mhpiReturnT ret;

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
      vpiHandle r = (vpiHandle) mhpi_get_vpi_handle(h);
      int res = uvm_hdl_set_vlog(r, path, valuep, vpiReleaseFlag);
      mhpi_release_handle(h); 
      return res;
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
      mhpiHandleT mhpi_mhRegion = mhpi_handle(mhpiScope, h);
      ret = mhpi_release_force(path, mhpi_mhRegion);
      mhpi_release_handle(h); 
      if (ret == mhpiRetOk) {
        return(1);
      }
      else 
        return(0);

    }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_RELEASE",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
      mhpi_release_handle(h); 
#endif      
      return (0);
    }
#else
    mhpiHandleT h = mhpi_handle_by_name(path, 0);
    mhpiReturnT ret;

    if (mhpi_get(mhpiPliP, h) == mhpiVpiPli) {
      mhpi_release_parent_handle(h);  
      return uvm_hdl_set_vlog(path, valuep, vpiReleaseFlag);
    }
    else if (mhpi_get(mhpiPliP, h) == mhpiVhpiPli) {
      mhpiHandleT mhpi_mhRegion = mhpi_handle(mhpiScope, h);
      mhpi_release_parent_handle(h);  
      ret = mhpi_release_force(path, mhpi_mhRegion);
      if (ret == mhpiRetOk) {
        return(1);
      }
      else
        return(0);

      }
    else {
#ifdef VCSMX_ERROR_ON_NULL_HANDLE
      const char * err_str = "set: unable to locate hdl path (%s)\n Either the name is incorrect, or you may not have PLI/ACC visibility to that name";
      char buffer[strlen(err_str) + strlen(path)];
      sprintf(buffer, err_str, path);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/HDL_RELEASE",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,

                       __LINE__);
#endif
      return (0);
    }
#endif
#endif
}

