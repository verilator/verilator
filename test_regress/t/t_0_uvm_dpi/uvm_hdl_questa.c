//----------------------------------------------------------------------
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2009-2023 Mentor Graphics Corporation
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


#include "uvm_dpi.h"


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


// Required to give VHDL back-door access via the FLI
#include <mti.h>
#define MTI_RELEASE_SIGNAL ((mtiForceTypeT)(-1))

/*
 * FUNCTION -- NODOCS -- uvm_is_vhdl_path
 *
 * Given a string path, use the FLI to find the named signal.
 * Strip off any bit select applied to a vector
 *
 */
int uvm_is_vhdl_path(char *path) {

  char *path_ptr = path;
  int path_len;

  mtiSignalIdT signal_id;

  path_len = strlen(path);
  path_ptr = (char*)(path+path_len-1);
  if (*path_ptr != ']') {
    signal_id = mti_FindSignal(path);
  } else {
    while(path_ptr != path && *path_ptr != '[') {
      path_ptr--;
      path_len--;
    }
    if(path == path_ptr) {
      return 0; // Something strange about string
    }
    if(*path_ptr == '[') {
      path_len--;
    }

    char path_copy[path_len+1];
    int i;
    for(i = 0; i < path_len; i++) {
       path_copy[i] = path[i];
    }    

    path_copy[path_len]='\0';
    signal_id = mti_FindSignal(path_copy);
  }
  if (signal_id) {
    return 1;
  } else {
    return 0;
  }
}






/*
 * FUNCTION -- NODOCS -- string_to_vecval
 *
 * Given a string, and the number of bits,
 * set the Verilog aval/bval in 'value'.
 *
 * The string will contain 'nbits' characters, either
 * '0', '1', 'x' or 'z'.
 *
 */
void
string_to_vecval(char *s, int nbits, p_vpi_vecval value)
{
  char *p;
  int j, k;
  int bits_assigned;
  int chunks;
  int abit, bbit;
  char c;

  p = s;
  chunks = (nbits-1)/32 + 1;
  bits_assigned = 0;

  for(j=0;j<chunks; ++j) {
    value[j].aval = 0;
    value[j].bval = 0;
    for(k=0;k<32;k++) {
      c = *p++;
      if      (c == '1') { abit = 1; bbit = 0; }
      else if (c == '0') { abit = 0; bbit = 0; }
      else if (c == 'x') { abit = 1; bbit = 1; }
      else if (c == 'z') { abit = 0; bbit = 1; }
      else { abit = 0; bbit = 0; }

      value[j].aval = value[j].aval << 1;
      value[j].bval = value[j].bval << 1;

      value[j].aval |= abit;
      value[j].bval |= bbit;

      if (++bits_assigned >= nbits)
        break;
    }
  }
}

/*
 * FUNCTION -- NODOCS -- vecval_to_string
 *
 * Given a vecval (logic verilog type), return
 * a string representation. The returned
 * string will contain 'nbits' characters, either
 * '0', '1', 'x' or 'z'.
 *
 * For example:
 *   vecval_to_string(8, 8'b0000_0001)
 *   vecval_to_string(8, 8'b0000_00x1)
 *
 * returns:
 *   "00000001"
 *   "000000x1"
 */
char *
vecval_to_string(int nbits, p_vpi_vecval value)
{
  static char *string_buffer      = 0;
  static int   string_buffer_size = 16;

  char *p;
  int j, k;
  int bits_assigned;
  int chunks;
  int abit, bbit;
  char c;

  /* First time, or nbits is really big. */
  if ((string_buffer == 0) ||
      (nbits > string_buffer_size-1)) {
      /* nbits is really big. Make it even
       * bigger - to avoid coming in here too many times.
       */
      if (nbits > string_buffer_size-1)
          string_buffer_size = nbits * 2;
      string_buffer = (char *)malloc(string_buffer_size);
  }

  p = string_buffer + nbits;
  *p = 0;

  chunks = (nbits-1)/32 + 1;
  bits_assigned = 0;

  for(j=0;j<chunks; ++j) {
    for(k=0;k<32;k++) {
      abit = (value[j].aval>>k) & 0x01;
      bbit = (value[j].bval>>k) & 0x01;

      if      ((abit == 1) && (bbit == 0)) c = '1';
      else if ((abit == 0) && (bbit == 0)) c = '0';
      else if ((abit == 1) && (bbit == 1)) c = 'x';
      else if ((abit == 0) && (bbit == 1)) c = 'z';
      else { c = 'x'; }

      p--;
      *p = c;
      if (++bits_assigned >= nbits)
        break;
    }
  }
  return string_buffer;
}

/*
 * FUNCTION -- NODOCS -- string2vhdl_array_of_int
 *
 * Given a string of '0', '1', 'x', 'z', convert
 * that to a VHDL array of ints.
 */
void
string2vhdl_array_of_int(mtiInt32T *array,
        unsigned int elements, char *s)
{
    unsigned int i;
    char c;

    if (strlen(s) != elements) {
      vpi_printf((PLI_BYTE8*)"FLI: Error: string2vhdl_array_of_int\n");
      vpi_printf((PLI_BYTE8*)"FLI:        Length of values %0d does\n",
                 strlen(s));
      vpi_printf(
        (PLI_BYTE8*)"FLI:        NOT match the number of elements (%d)\n",
                 elements);
        tf_dofinish();
    }

    for(i = 0; i < elements; i++) {
        c = *s++;
             if (c == '0') array[i] = 2;
        else if (c == '1') array[i] = 3;
        else if (c == 'x') array[i] = 1;
        else if (c == 'z') array[i] = 4;
    }
}

/*
 * FUNCTION -- NODOCS -- string2vhdl_array_of_char
 *
 * Given a string of '0', '1', 'x', 'z', convert
 * that to a VHDL array of ints.
 */
void
string2vhdl_array_of_char(char *array, unsigned int elements, char *s)
{
    unsigned int i;
    char c;

    if (strlen(s) != elements) {
        vpi_printf((PLI_BYTE8*)"FLI: Error: string2vhdl_array_of_char\n");
        tf_dofinish();
    }

    for(i = 0; i < elements; i++) {
        c = *s++;
             if (c == '0') array[i] = 2;
        else if (c == '1') array[i] = 3;
        else if (c == 'x') array[i] = 1;
        else if (c == 'z') array[i] = 4;
    }
}


/*
 * FUNCTION -- NODOCS -- vhdl_array_of_char2string
 *
 * Given an array of VHDL values, convert them
 * to a string of '0', '1', 'x' or 'z'.
 */
char *
vhdl_array_of_char2string(char *array, int elements)
{
    int i;
    char *s;
    char *p;
    char c;

    s = (char *)malloc(elements+1);
    p = s;
    for(i = 0; i < elements; i++) {
             if (array[i] == 2) c = '0';
        else if (array[i] == 3) c = '1';
        else if (array[i] == 1) c = 'x';
        else if (array[i] == 4) c = 'z';
        else                    c = '-';
        *p++ = c;
    }
    *p = 0;
    return s;
}

/*
 * FUNCTION -- NODOCS -- vhdl_array_of_int2string
 *
 * Given an array of VHDL values, convert them
 * to a string of '0', '1', 'x' or 'z'.
 */
char *
vhdl_array_of_int2string(int *array, int elements)
{
    int i;
    char *s;
    char *p;
    char c;

    s = (char *)malloc(elements+1);
    p = s;
    for(i = 0; i < elements; i++) {
             if (array[i] == 2) c = '0';
        else if (array[i] == 3) c = '1';
        else if (array[i] == 1) c = 'x';
        else if (array[i] == 4) c = 'z';
        else                    c = '-';
        *p++ = c;
    }
    *p = 0;
    return s;
}


/*
 * FUNCTION -- NODOCS -- uvm_register_get_vhdl
 *
 * Used to get the value of a VHDL signal, and return
 * the value as a Verilog aval/bval pair.
 */

int uvm_register_get_vhdl(char *path, p_vpi_vecval value)
{
    mtiSignalIdT signal_id;
    mtiTypeIdT   signal_type;
    char *char_array;
    int nbits = 0;

    char *path_ptr = path;
    int path_len;

    path_len = strlen(path);
    path_ptr = (char*)(path+path_len-1);

    if(*path_ptr != ']') {
      // Not a vectored access
      signal_id = mti_FindSignal(path);
      if (signal_id) {
        char_array = (char*)mti_GetArraySignalValue(signal_id, 0);
        signal_type = mti_GetSignalType(signal_id);
        if(mti_GetTypeKind(signal_type) == MTI_TYPE_ARRAY) {
          nbits = mti_TickLength(signal_type);
      } else {
      nbits = 1; // Has to be a scalar signal
      }
        string_to_vecval(
          vhdl_array_of_char2string(char_array, nbits),
          nbits,
          value);
        mti_VsimFree(char_array);
        return 1;
      } else {
         vpi_printf(
           (PLI_BYTE8*)"FLI: uvm_register_get_vhdl() failed. Cannot find signal '%s'\n",
           path);
           return 0;
      }
    } else {
      // A vectored access
      while(path_ptr != path && *path_ptr != '[') {
        path_ptr--;
        path_len--;
      }
      // Extract the range from the path
      int lhs, rhs, width, incr;

      path_len--;
      char path_copy[1024];
      strncpy(path_copy, path, path_len);
      path_copy[path_len]='\0';

      // Find out no of bits in vector
      signal_id = mti_FindSignal(path_copy);
      if (signal_id) {
        char_array = (char*)mti_GetArraySignalValue(signal_id, 0);
        signal_type = mti_GetSignalType(signal_id);
        if(mti_GetTypeKind(signal_type) == MTI_TYPE_ARRAY) {
          nbits = mti_TickLength(signal_type);
        } else {
          if(mti_GetTypeKind(signal_type) == MTI_TYPE_ENUM) {
          nbits = 1;
          }
        }
        if(strchr(path_ptr, ':') != NULL) {

          if(sscanf(path_ptr,"[%u:%u]",&lhs, &rhs)) {
            int i;
            incr = (lhs>rhs) ? 1 : -1;
            width = (lhs>rhs) ? lhs-rhs+1 : rhs-lhs+1;
            char* vectors = vhdl_array_of_char2string(char_array, nbits);
            char reduced_vector[256];
            for (i = 0; i < width; i++) {
              reduced_vector[i] = vectors[(nbits-1)-lhs];
              lhs -= incr;
            }
            string_to_vecval(reduced_vector, width, value);
          } else {
            return 0;
          }
        } else {
          if(sscanf(path_ptr, "[%u]", &rhs)) {
            char* vectors = vhdl_array_of_char2string(char_array, nbits);
            char reduced_vector[256];
            reduced_vector[0] = vectors[(nbits-1)-rhs];
            string_to_vecval(reduced_vector, 1, value);
          } else {
            return 0;
          }
        }
          mti_VsimFree(char_array);
          return 1;

        } else {
          return 0;
        }


    }
}

/*
 * FUNCTION -- NODOCS -- uvm_register_set_vhdl
 *
 * Used to set the value of a VHDL signal, given
 * the value as a Verilog aval/bval pair.
 */
int uvm_register_set_vhdl(char *path, p_vpi_vecval value, mtiForceTypeT forceType)
{
    mtiSignalIdT signal_id;
    mtiTypeIdT   signal_type;

    char      *char_array;
    char *path_ptr = path;
    int path_len;

    int nbits = 0;
    path_len = strlen(path);
    path_ptr = (char*)(path+path_len-1);

    vpi_printf((PLI_BYTE8*)"Setting vhdl path %s\n", path);

    if(*path_ptr != ']') {
      // Not a vectored access
      signal_id = mti_FindSignal(path);
      if (signal_id) {
        char_array = (char*)mti_GetArraySignalValue(signal_id, 0);
        signal_type = mti_GetSignalType(signal_id);
        if(mti_GetTypeKind(signal_type) == MTI_TYPE_ARRAY) {
          nbits = mti_TickLength(signal_type);
        } else {
          if(mti_GetTypeKind(signal_type) == MTI_TYPE_ENUM) {
          nbits = 1;
          }
        }
		if (forceType == MTI_RELEASE_SIGNAL) {
        	mti_ReleaseSignal(signal_id);
		} else {
        	mti_ForceSignal(signal_id, vecval_to_string(nbits, value), 0, forceType, -1, -1);
		}
        mti_VsimFree(char_array);
        return 1;
      } else {
         vpi_printf(
          (PLI_BYTE8*)"FLI: uvm_register_set_vhdl() failed. Cannot find signal '%s'\n",
           path);
         return 0;
      }
    } else {
      // A vectored access:
      while(path_ptr != path && *path_ptr != '[') {
        path_ptr--;
        path_len--;
      }
      // Extract the range from the path
      int lhs, rhs, width, incr;

      path_len--;
      char path_copy[1024];
      strncpy(path_copy, path, path_len);
      path_copy[path_len]='\0';

      // Find out no of bits in vector
      signal_id = mti_FindSignal(path_copy);
      if (signal_id) {
        char_array = (char*)mti_GetArraySignalValue(signal_id, 0);
        signal_type = mti_GetSignalType(signal_id);
        if(mti_GetTypeKind(signal_type) == MTI_TYPE_ARRAY) {
          nbits = mti_TickLength(signal_type);
        } else {
          if(mti_GetTypeKind(signal_type) == MTI_TYPE_ENUM) {
          nbits = 1;
          }
        }
      }

      if(strchr(path_ptr, ':') != NULL) {
        if(sscanf(path_ptr,"[%u:%u]",&lhs, &rhs)) {
          int i;
          char index_str[20];
          char path_str[80];
          char vector_val[128];

          strcpy(vector_val,vecval_to_string(nbits, value));
          incr = (lhs>rhs) ? 1 : -1;
          width = (lhs>rhs) ? lhs-rhs+1 : rhs-lhs+1;

          for (i = 0; i < width; i++) {
            sprintf(index_str,"(%u)",rhs);
            rhs += incr;
            strcpy(path_str, path_copy);
            strcat(path_str,index_str);
            signal_id = mti_FindSignal(path_str);
			if (forceType == MTI_RELEASE_SIGNAL) {
              mti_ReleaseSignal(signal_id);
			} else {
              if(vector_val[(nbits-i)-1] == '1') {
                mti_ForceSignal(signal_id, (char*)"1", 0, MTI_FORCE_DEPOSIT, -1, -1);
              } else {
                mti_ForceSignal(signal_id, (char*)"0", 0, MTI_FORCE_DEPOSIT, -1, -1);
              }
			}
          }
        }
      } else {
        vpi_printf((PLI_BYTE8*)"Single vector\n");
        if(sscanf(path_ptr,"[%u]", &rhs)) {
          char index_str[20];
          char path_str[80];
          char vector_val[128];

          strcpy(vector_val,vecval_to_string(nbits, value));
            sprintf(index_str,"(%u)",rhs);
            strcpy(path_str, path_copy);
            strcat(path_str,index_str);
            signal_id = mti_FindSignal(path_str);
			if (forceType == MTI_RELEASE_SIGNAL) {
              mti_ReleaseSignal(signal_id);
			} else {
              if(vector_val[(nbits-1)-rhs] == '1') {
                mti_ForceSignal(signal_id, (char*)"1", 0, MTI_FORCE_DEPOSIT, -1, -1);
              } else {
                mti_ForceSignal(signal_id, (char*)"0", 0, MTI_FORCE_DEPOSIT, -1, -1);
              }
			}
          }


      }

      mti_VsimFree(char_array);
      return 1;
    }

}

//

static int uvm_hdl_set_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static int uvm_hdl_get_vlog(char *path, p_vpi_vecval value, PLI_INT32 flag);
static int partsel = 0;

/*
 * Given a path with part-select, break into individual bit accesses
 * path = pointer to user string
 * value = pointer to logic vector
 * flag = deposit vs force/release options, etc
 */
static int uvm_hdl_set_vlog_partsel(char *path, p_vpi_vecval value, PLI_INT32 flag)
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
    vpi_printf((PLI_BYTE8*)"LHS %u RHS %u\n", lhs, rhs);

    // perform set for each individual bit
    for (i=0; i < width; i++) {
      sprintf(index_str,"%u]",rhs);
      strncpy(path_ptr,index_str,path_len);
      svGetPartselLogic(&bit_value,value,i,1);
      rhs += incr;
      if (!uvm_hdl_set_vlog(path,&bit_value,flag))
        return 0;
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
    partsel = 1;
    for (i=0; i < width; i++) {
      int result;
      svLogic logic_bit;
      sprintf(index_str,"%u]",rhs);
      strncpy(path_ptr,index_str,path_len);
      result = uvm_hdl_get_vlog(path,&bit_value,flag);
      logic_bit = svGetBitselLogic(&bit_value,0);
      svPutPartselLogic(value,bit_value,i,1);
      rhs += incr;
      if (!result)
        return 0;
    }
    partsel = 0;
    return 1;
  }
  return 0;
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


  int result = 0;
  result = uvm_hdl_set_vlog_partsel(path,value,flag);
  if (result < 0)
    return 0;
  if (result == 1)
    return 1;

  if (!strncmp(path,"$root.",6))
    r = vpi_handle_by_name(path+6, 0);
  else
    r = vpi_handle_by_name(path, 0);

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
    }
    value_s.format = vpiVectorVal;
    value_s.value.vector = value;
    vpi_put_value(r, &value_s, &time_s, flag);
    if (value == NULL) {
      value = value_s.value.vector;
    }
  }
  vpi_release_handle(r);
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

  if (!partsel) {
    maxsize = uvm_hdl_max_width();
    chunks = (maxsize-1)/32 + 1;
    for(i=0;i<chunks-1; ++i) {
      value[i].aval = 0;
      value[i].bval = 0;
    }
  }
  int result = 0;
  result = uvm_hdl_get_vlog_partsel(path,value,flag);
  if (result < 0)
    return 0;
  if (result == 1)
    return 1;

  if (!strncmp(path,"$root.",6))
    r = vpi_handle_by_name(path+6, 0);
  else
    r = vpi_handle_by_name(path, 0);

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


/*
 * Given a path, look the path name up using the PLI,
 * but don't set or get. Just check.
 *
 * Return 0 if NOT found.
 * Return 1 if found.
 */
int uvm_hdl_check_path(char *path)
{
  vpiHandle r;

  // Check VHDL for Questa
  if(uvm_is_vhdl_path(path)) {
    return 1;
  }

  if (!strncmp(path,"$root.",6)) {
    r = vpi_handle_by_name(path+6, 0);
  } else
    r = vpi_handle_by_name(path, 0);

  if(r == 0)
    return 0;
  else
    return 1;
}


/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and return its 'value'.
 */
int uvm_hdl_read(char *path, p_vpi_vecval value)
{
  if (uvm_is_vhdl_path(path)) {
    return uvm_register_get_vhdl(path, value);
  } else {
    return uvm_hdl_get_vlog(path, value, vpiNoDelay);
  }
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_deposit(char *path, p_vpi_vecval value)
{
  if(uvm_is_vhdl_path(path)) {
    return uvm_register_set_vhdl(path, value, MTI_FORCE_DEPOSIT);
  } else {
    return uvm_hdl_set_vlog(path, value, vpiNoDelay);
  }
}


/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and set it to 'value'.
 */
int uvm_hdl_force(char *path, p_vpi_vecval value)
{
  if(uvm_is_vhdl_path(path)) {
    return uvm_register_set_vhdl(path, value, MTI_FORCE_FREEZE);
  } else {
    return uvm_hdl_set_vlog(path, value, vpiForceFlag);
  }
}


/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release_and_read(char *path, p_vpi_vecval value)
{
  int result = 0;
  if(uvm_is_vhdl_path(path)) {
    result = uvm_register_set_vhdl(path, value, MTI_RELEASE_SIGNAL);
	if (result > 0)
      result = uvm_register_get_vhdl(path, value);
  } else {
    result = uvm_hdl_set_vlog(path, value, vpiReleaseFlag);
	if (result > 0)
    result = uvm_hdl_get_vlog(path, value, vpiNoDelay);
  }
  return result;
}

/*
 * Given a path, look the path name up using the PLI
 * or the FLI, and release it.
 */
int uvm_hdl_release(char *path)
{
  s_vpi_vecval value;
  p_vpi_vecval valuep = &value;
  if(uvm_is_vhdl_path(path)) {
    return uvm_register_set_vhdl(path, valuep, MTI_RELEASE_SIGNAL);
  } else {
    return uvm_hdl_set_vlog(path, valuep, vpiReleaseFlag);
  }
}

