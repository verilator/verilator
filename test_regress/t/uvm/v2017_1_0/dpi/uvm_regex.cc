//----------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2013-2014 NVIDIA Corporation
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


#include "uvm_dpi.h"
#include <sys/types.h>


const char uvm_re_bracket_char = '/';
#define UVM_REGEX_MAX_LENGTH 2048
static char uvm_re[UVM_REGEX_MAX_LENGTH+4];

static const char* empty_regex="/^$/";

//--------------------------------------------------------------------
// uvm_re_match
//
// Match a string to a regular expression.  The regex is first lookup
// up in the regex cache to see if it has already been compiled.  If
// so, the compile version is retrieved from the cache.  Otherwise, it
// is compiled and cached for future use.  After compilation the
// matching is done using regexec().
//--------------------------------------------------------------------
int uvm_re_match(const char * re, const char *str)
{
  regex_t *rexp;
  int err;

  // safety check.  Args should never be ~null~ since this is called
  // from DPI.  But we'll check anyway.
  if(re == NULL)
    return 1;
  if(str == NULL)
    return 1;

  int len = strlen(re);
  char * rex = &uvm_re[0];

  if (len > UVM_REGEX_MAX_LENGTH) {
      const char* err_str = "uvm_re_match : regular expression greater than max %0d: |%s|";
      char buffer[strlen(err_str) + int_str_max(10) + strlen(re)];
      sprintf(buffer, err_str, UVM_REGEX_MAX_LENGTH, re);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/REGEX_MAX",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
    return 1;
  }

  // we copy the regexp because we need to remove any brackets around it
  strncpy(&uvm_re[0],re,UVM_REGEX_MAX_LENGTH);
  if (len>1 && (re[0] == uvm_re_bracket_char) && re[len-1] == uvm_re_bracket_char) {
    uvm_re[len-1] = '\0';
    rex++;
  }

  rexp = (regex_t*)malloc(sizeof(regex_t));

  if (rexp == NULL) {
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/REGEX_ALLOC",
                       (char*) "uvm_re_match: internal memory allocation error",
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
    return 1;
  }

  err = regcomp(rexp, rex, REG_EXTENDED);

  if (err != 0) {
      regerror(err,rexp,uvm_re,UVM_REGEX_MAX_LENGTH-1);
      const char * err_str = "uvm_re_match : invalid glob or regular expression: |%s||%s|";
      char buffer[strlen(err_str) + strlen(re) + strlen(uvm_re)+1];
      sprintf(buffer, err_str, re, uvm_re);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/REGEX_INV",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
    regfree(rexp);
    free(rexp);
    return err;
  }

  err = regexec(rexp, str, 0, NULL, 0);

  //vpi_printf((PLI_BYTE8*)  "UVM_INFO: uvm_re_match: re=%s str=%s ERR=%0d\n",rex,str,err);
  regfree(rexp);
  free(rexp);

  return err;
}


//--------------------------------------------------------------------
// uvm_glob_to_re
//
// Convert a glob expression to a normal regular expression.
//--------------------------------------------------------------------

const char * uvm_glob_to_re(const char *glob)
{
  const char *p;
  int len;

  // safety check.  Glob should never be ~null~ since this is called
  // from DPI.  But we'll check anyway.
  if(glob == NULL)
    return NULL;

  len = strlen(glob);

  if (len > 2040) {
      const char * err_str = "uvm_re_match : glob expression greater than max 2040: |%s|";
      char buffer[strlen(err_str) + strlen(glob)+1];
      sprintf(buffer, err_str, glob);
      m_uvm_report_dpi(M_UVM_ERROR,
                       (char*) "UVM/DPI/REGEX_MAX",
                       &buffer[0],
                       M_UVM_NONE,
                       (char*)__FILE__,
                       __LINE__);
    return glob;
  }

  // If either of the following cases appear then return an empty string
  //
  //  1.  The glob string is empty (it has zero characters)
  //  2.  The glob string has a single character that is the
  //      uvm_re_bracket_char  (i.e. "/")
  if(len == 0 || (len == 1 && *glob == uvm_re_bracket_char))
  {
    return empty_regex;
  }

  // If bracketed with the /glob/, then it's already a regex
  if(glob[0] == uvm_re_bracket_char && glob[len-1] == uvm_re_bracket_char)
  {
    strcpy(uvm_re,glob);
    return &uvm_re[0];
  }
  else
  {
    // Convert the glob to a true regular expression (Posix syntax)
    len = 0;

    uvm_re[len++] = uvm_re_bracket_char;

    // ^ goes at the beginning...
    if (*glob != '^')
      uvm_re[len++] = '^';

    for(p = glob; *p; p++)
    {
      // Replace the glob metacharacters with corresponding regular
      // expression metacharacters.
      switch(*p)
      {
      case '*':
        uvm_re[len++] = '.';
        uvm_re[len++] = '*';
        break;

      case '+':
        uvm_re[len++] = '.';
        uvm_re[len++] = '+';
        break;

      case '.':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '.';
        break;

      case '?':
        uvm_re[len++] = '.';
        break;

      case '[':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '[';
        break;

      case ']':
        uvm_re[len++] = '\\';
        uvm_re[len++] = ']';
        break;

      case '(':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '(';
        break;

      case ')':
        uvm_re[len++] = '\\';
        uvm_re[len++] = ')';
        break;

      default:
        uvm_re[len++] = *p;
        break;
      }
    }
  }

  // Let's check to see if the regular expression is bounded by ^ at
  // the beginning and $ at the end.  If not, add those characters in
  // the appropriate position.

  if (uvm_re[len-1] != '$')
    uvm_re[len++] = '$';

  uvm_re[len++] = uvm_re_bracket_char;

  uvm_re[len++] = '\0';

  return &uvm_re[0];
}
