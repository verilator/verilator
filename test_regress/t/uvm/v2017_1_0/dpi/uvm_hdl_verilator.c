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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void m_uvm_error(const char *ID, const char *msg, ...);
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value);
static int uvm_hdl_max_width();

// static print buffer
static char m_uvm_temp_print_buffer[1024];

// static print error
static void m_uvm_error(const char *id, const char *msg, ...) {
  va_list argptr;
  va_start(argptr, msg);
  vsnprintf(m_uvm_temp_print_buffer, sizeof(m_uvm_temp_print_buffer), msg, argptr);
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
      vpi_release_handle(ms);
    }
  }
  return UVM_HDL_MAX_WIDTH;
}

/*
 * Given a path, look the path name up using the PLI,
 * and set it to 'value'.
 */
static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag) {
  vpiHandle r;
  s_vpi_value value_s = {vpiIntVal, {0}};
  s_vpi_time time_s = {vpiSimTime, 0, 0, 0.0};
  int i, size, chunks;
  static int s_maxsize = -1;

  if (path == NULL || path[0] == '\0') {
    m_uvm_error("UVM/DPI/VLOG_PUT", "NULL or empty HDL path passed to uvm_hdl_set_vlog");
    return 0;
  }

  r = vpi_handle_by_name(path, 0);
  if (r == 0) {
    m_uvm_error("UVM/DPI/VLOG_PUT",
                "set: unable to locate hdl path (%s)\n Either the name is incorrect, "
                "or you may not have PLI/ACC visibility to that name",
                path);
    return 0;
  }

  if (value == NULL && flag != vpiReleaseFlag) {
    m_uvm_error("UVM/DPI/VLOG_PUT",
                "NULL value pointer passed for hdl path '%s' in non-release operation", path);
    vpi_release_handle(r);
    return 0;
  }

  if (value) {
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
  }

  value_s.format = value ? vpiVectorVal : vpiSuppressVal;
  value_s.value.vector = value;
  vpiHandle returnHandle = vpi_put_value(r, &value_s, &time_s, flag);
  if (returnHandle == 0) {
    vpi_release_handle(r);
    m_uvm_error("UVM/DPI/VLOG_PUT",
                "failed to set hdl path '%s'. Common reasons include a signal having an "
                "unsupported type, such as a real or a string, or attempting to force a signal "
                "that is not marked as /*verilator forceable*/",
                path);
    return 0;
  }

  if (flag == vpiReleaseFlag && value) {
    chunks = (size - 1) / 32 + 1;
    for (i = 0; i < chunks; ++i) value[i] = value_s.value.vector[i];
  }

  vpi_release_handle(r);

  return 1;
}

/*
 * Given a path, look the path name up using the PLI
 * and return its 'value'.
 */
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value) {
  static int s_maxsize = -1;
  int i, size, chunks;
  vpiHandle r;
  s_vpi_value value_s = {vpiVectorVal, {0}};

  if (path == NULL || path[0] == '\0') {
    m_uvm_error("UVM/DPI/VLOG_GET", "NULL or empty HDL path passed to uvm_hdl_get_vlog");
    return 0;
  }

  r = vpi_handle_by_name(path, 0);
  if (r == 0) {
    m_uvm_error("UVM/DPI/VLOG_GET",
                "unable to locate hdl path (%s)\n Either the name is incorrect, or you "
                "may not have PLI/ACC visibility to that name",
                path);
    return 0;
  }

  if (value == NULL) {
    m_uvm_error("UVM/DPI/VLOG_GET", "NULL value pointer passed for hdl path '%s'", path);
    vpi_release_handle(r);
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

  value_s.value.vector = NULL;
  vpi_get_value(r, &value_s);
  if (value_s.format != vpiVectorVal || value_s.value.vector == 0) {
    m_uvm_error("UVM/DPI/VLOG_GET",
                "failed to get value for hdl path '%s'. Common reasons include a signal having an "
                "unsupported type, such as a real or a string",
                path);
    vpi_release_handle(r);
    return 0;
  }

  // Note upper bits are not cleared, other simulators do likewise
  for (i = 0; i < chunks; ++i) {
    value[i].aval = value_s.value.vector[i].aval;
    value[i].bval = value_s.value.vector[i].bval;
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

  if (path == NULL || path[0] == '\0') {
    m_uvm_error("UVM/DPI/VLOG_CHECK", "NULL or empty HDL path passed to uvm_hdl_check_path");
    return 0;
  }

  handle = vpi_handle_by_name(path, 0);
  if (handle) vpi_release_handle(handle);
  return (handle != 0);
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and return its 'value'.
 */
int uvm_hdl_read(char *path, p_vpi_vecval value) { return uvm_hdl_get_vlog(path, value); }

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
int uvm_hdl_release(char *path) { return uvm_hdl_set_vlog(path, NULL, vpiReleaseFlag); }
