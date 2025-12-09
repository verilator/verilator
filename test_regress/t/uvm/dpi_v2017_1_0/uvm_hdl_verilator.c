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

#include "svdpi.h"
#include "vpi_user.h"

#include <malloc.h>
#include <stdio.h>
#include <string.h>

static void m_uvm_error(const char *ID, const char *msg, ...);
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag, int partsel);
static int uvm_hdl_max_width();

// static print buffer
static char m_uvm_temp_print_buffer[1024];

// static print error
static void m_uvm_error(const char *id, const char *msg, ...) {
  va_list argptr;
  va_start(argptr, msg);
  vsprintf(m_uvm_temp_print_buffer, msg, argptr);
  va_end(argptr);
  m_uvm_report_dpi(M_UVM_ERROR, (char *)id, &m_uvm_temp_print_buffer[0], M_UVM_NONE,
                   (char *)__FILE__, __LINE__);
}

/*
 * UVM HDL access C code.
 *
 */

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
static int UVM_HDL_MAX_WIDTH = 0;
static int uvm_hdl_max_width() {
  if (!UVM_HDL_MAX_WIDTH) {
    vpiHandle ms;
    s_vpi_value value_s = {vpiIntVal, {0}};
    ms = vpi_handle_by_name((PLI_BYTE8 *)"uvm_pkg::UVM_HDL_MAX_WIDTH", 0);
    if (ms == 0) {
      UVM_HDL_MAX_WIDTH = 1024; /* If nothing else is defined, this is the DEFAULT */
    } else {
      vpi_get_value(ms, &value_s);
      UVM_HDL_MAX_WIDTH = value_s.value.integer;
    }
  }
  return UVM_HDL_MAX_WIDTH;
}

/*
 * Internals: Given a path, look at the path name and determine
 * the handle and any partsel's needed to access it.
 */
static vpiHandle uvm_hdl_handle_by_name_partsel(char *path, int *is_partsel_ptr, int *hi_ptr,
                                                int *lo_ptr) {
  vpiHandle r;
  char *path_ptr;
  char *path_base_ptr;
  int temp;
  *is_partsel_ptr = 0;

  if (!path || !path[0]) return 0;

  // If direct lookup works, go with that
  r = vpi_handle_by_name(path, 0);
  if (r) return r;

  // Find array subscript
  path_ptr = (char *)(path + strlen(path) - 1);
  if (*path_ptr != ']') return 0;

  while (path_ptr != path && *path_ptr != ':' && *path_ptr != '[') --path_ptr;
  if (path_ptr == path) return 0;
  *lo_ptr = *hi_ptr = atoi(path_ptr + 1);
  *is_partsel_ptr = 1;

  if (*path_ptr == ':') {
    --path_ptr;  // back over :

    while (path_ptr != path && *path_ptr != '[') --path_ptr;
    *hi_ptr = atoi(path_ptr + 1);
    if (path_ptr == path) return 0;
  }

  if (*lo_ptr > *hi_ptr) {
    temp = *lo_ptr;
    *lo_ptr = *hi_ptr;
    *hi_ptr = temp;
  }

  path_base_ptr = strndup(path, (path_ptr - path));

  r = vpi_handle_by_name(path_base_ptr, 0);
  if (!r) return 0;

  {
    vpiHandle rh;
    s_vpi_value value;
    int decl_ranged = 0;
    int decl_lo;
    int decl_hi;
    int decl_left = -1;
    int decl_right = -1;
    rh = vpi_handle(vpiLeftRange, r);
    if (rh) {
      value.format = vpiIntVal;
      vpi_get_value(rh, &value);
      decl_left = value.value.integer;
      vpi_release_handle(rh);
    }
    rh = vpi_handle(vpiRightRange, r);
    if (rh) {
      value.format = vpiIntVal;
      vpi_get_value(rh, &value);
      decl_ranged = 1;
      decl_right = value.value.integer;
      vpi_release_handle(rh);
    }
    if (!decl_ranged) {
      // vpi_printf((PLI_BYTE8 *)"Outside declaration '%s' range %d:%d\n",
      //            path, decl_left, decl_right);
      return 0;
    }
    // vpi_printf((PLI_BYTE8 *)"%s:%d: req %d:%d decl %d:%d for '%s'\n",
    //            __FILE__, __LINE__, *hi_ptr, *lo_ptr, decl_left, decl_right, path);
    decl_lo = (decl_left < decl_right) ? decl_left : decl_right;
    decl_hi = (decl_left > decl_right) ? decl_left : decl_right;
    if (*lo_ptr < decl_lo) return 0;
    if (*hi_ptr > decl_hi) return 0;
    *lo_ptr -= decl_lo;
    *hi_ptr -= decl_lo;
  }
  return r;
}

/*
 * Given a path, look the path name up using the PLI,
 * and set it to 'value'.
 */
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag) {
  vpiHandle r;
  s_vpi_value value_s = {vpiIntVal, {0}};
  s_vpi_time time_s = {vpiSimTime, 0, 0, 0.0};
  int is_partsel, hi, lo;
  int size;
  static int s_maxsize = -1;

  if (flag == vpiForceFlag || flag == vpiReleaseFlag) {
    // It appears other simulator interfaces likewise don't support this
    m_uvm_error("UVM/DPI/VLOG_GET", "Unsupported: uvh_hdl_force/uvm_hdl_release on hdl path '%s'",
                path);
    return 0;
  }

  r = uvm_hdl_handle_by_name_partsel(path, &is_partsel, &hi, &lo);
  if (r == 0) {
    m_uvm_error("UVM/DPI/HDL_SET",
                "set: unable to locate hdl path (%s)\n Either the name is incorrect, "
                "or you may not have PLI/ACC visibility to that name",
                path);
    return 0;
  }

  if (!is_partsel) {
    value_s.format = vpiVectorVal;
    value_s.value.vector = value;
    vpi_put_value(r, &value_s, &time_s, flag);
  } else {
    if (s_maxsize == -1) s_maxsize = uvm_hdl_max_width();
    size = vpi_get(vpiSize, r);
    if (size > s_maxsize) {
      m_uvm_error("UVM/DPI/VLOG_PUT",
                  "hdl path '%s' is %0d bits, but the maximum size is %0d.  "
                  "You can increase the maximum via a compile-time flag: "
                  "+define+UVM_HDL_MAX_WIDTH=<value>",
                  path, size, s_maxsize);
      vpi_release_handle(r);
      return 0;
    }

    value_s.format = vpiVectorVal;
    vpi_get_value(r, &value_s);

    for (int i = 0; i < (((hi - lo + 1) / 32) + 1); ++i) {
      int subsize = hi - (lo + (i << 5)) + 1;
      if (subsize > 32) subsize = 32;
      svPutPartselLogic(&value_s.value.vector[i], value[i], lo + (i << 5), subsize);
    }
    vpi_put_value(r, &value_s, &time_s, flag);
  }

  vpi_release_handle(r);

  return 1;
}

/*
 * Given a path, look the path name up using the PLI
 * and return its 'value'.
 */
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag, int partsel) {
  static int s_maxsize = -1;
  int i, size, chunks;
  vpiHandle r;
  s_vpi_value value_s;
  int is_partsel, hi, lo;

  r = uvm_hdl_handle_by_name_partsel(path, &is_partsel, &hi, &lo);
  if (r == 0) {
    m_uvm_error("UVM/DPI/VLOG_GET",
                "unable to locate hdl path (%s)\n Either the name is incorrect, or you "
                "may not have PLI/ACC visibility to that name",
                path);
    return 0;
  }

  if (s_maxsize == -1) s_maxsize = uvm_hdl_max_width();
  size = vpi_get(vpiSize, r);
  if (size > s_maxsize) {
    m_uvm_error("UVM/DPI/VLOG_GET",
                "hdl path '%s' is %0d bits, but the maximum size is %0d.  "
                "You can increase the maximum via a compile-time flag: "
                "+define+UVM_HDL_MAX_WIDTH=<value>",
                path, size, s_maxsize);
    vpi_release_handle(r);
    return 0;
  }

  chunks = (size - 1) / 32 + 1;

  value_s.format = vpiVectorVal;
  vpi_get_value(r, &value_s);
  // Note upper bits are not cleared, other simulators do likewise
  if (!is_partsel) {
    // Keep as separate branch as subroutine can potentially inline and highly optimize
    for (i = 0; i < chunks; ++i) {
      value[i].aval = value_s.value.vector[i].aval;
      value[i].bval = value_s.value.vector[i].bval;
    }
  } else {
    // Verilator supports > 32 bit widths, which is an extension to IEEE DPI
    svGetPartselLogic(value, value_s.value.vector, lo, hi - lo + 1);
  }
  // vpi_printf((PLI_BYTE8 *)"uvm_hdl_get_vlog(%s,%0x)\n", path, value[0].aval);
  vpi_release_handle(r);

  return 1;
}

/*
 * Given a path, look the path name up using the PLI,
 * but don't set or get. Just check.
 *
 * Return 0 if NOT found.
 * Return 1 if found.
 */
int uvm_hdl_check_path(char *path) {
  vpiHandle handle;

  handle = vpi_handle_by_name(path, 0);
  return (handle != 0);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and return its 'value'.
 */
int uvm_hdl_read(char *path, p_vpi_vecval value) {
  return uvm_hdl_get_vlog(path, value, vpiNoDelay, 0);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_deposit(char *path, p_vpi_vecval value) {
  return uvm_hdl_set_vlog(path, value, vpiNoDelay);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_force(char *path, p_vpi_vecval value) {
  return uvm_hdl_set_vlog(path, value, vpiForceFlag);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release_and_read(char *path, p_vpi_vecval value) {
  return uvm_hdl_set_vlog(path, value, vpiReleaseFlag);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release(char *path) {
  s_vpi_vecval value;
  return uvm_hdl_set_vlog(path, &value, vpiReleaseFlag);
}
