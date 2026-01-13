//----------------------------------------------------------------------
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2023 Marvell International Ltd.
// Copyright 2007-2011 Mentor Graphics Corporation
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
#include <sys/types.h>


const char uvm_re_bracket_char = '/';
const char uvm_re_escape_char = '\\';
#define UVM_REGEX_MAX_LENGTH 2048

static const char* empty_regex="^$";
static const char* empty_regex_brackets = "/^$/";

typedef regex_t* regex_ptr;

//--------------------------------------------------------------------
// uvm_re_buffer
//
// Returns the current value of the uvm re buffer string.  Note that
// the contents are only valid until the next call to a uvm_re_* method.
//--------------------------------------------------------------------
char * uvm_re_buffer()
{
  static char buffer[UVM_REGEX_MAX_LENGTH+4];
  return &buffer[0];
}

//--------------------------------------------------------------------
// uvm_re_deglobbed
//
// Convert a glob expression to a normal regular expression.
//--------------------------------------------------------------------

const char * uvm_re_deglobbed(const char *glob, unsigned char with_brackets)
{
  char* buffer = uvm_re_buffer();
  const char *p;
  
  // safety check.  Glob should never be ~null~ since this is called
  // from DPI.  But we'll check anyway.
  if(glob == NULL) {
    sprintf(buffer, "uvm_glob_to_re called with glob=NULL");
    return NULL;
  }
  
  size_t glob_len;
  glob_len = strlen(glob);
  
  // If either of the following cases appear then return an empty string
  //
  //  1.  The glob string is empty (it has zero characters)
  //  2.  The glob string has a single character that is the
  //      uvm_re_bracket_char  (i.e. "/")
  if(glob_len == 0 || (glob_len == 1 && *glob == uvm_re_bracket_char)) {
    if (with_brackets) {
      return empty_regex_brackets;
    }
    else {
      return empty_regex;
    }
  }
  
  // If bracketed with the /glob/, then it's already a regex
  if (glob[0] == uvm_re_bracket_char && glob[glob_len-1] == uvm_re_bracket_char) {
    if (glob_len > UVM_REGEX_MAX_LENGTH) {
      sprintf(buffer, "uvm_glob_to_re() glob exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
      return NULL;
    }
    else {
      if (with_brackets) {
        strcpy(buffer,glob);
      }
      else {
        strncpy(buffer, &glob[1], glob_len-2);
        buffer[glob_len-2] = '\0';
      }
    }
  }
  else {
    // Convert the glob to a true regular expression (Posix syntax)
    size_t iter;
    iter = 0;
    
    // Add the opening bracket
    if (with_brackets) {
      glob_len += 1;
      if (glob_len > UVM_REGEX_MAX_LENGTH) {
        sprintf(buffer, "uvm_glob_to_re glob expansion exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
        return NULL;
      }
      buffer[iter++] = uvm_re_bracket_char;
    }
    
    // ^ goes at the beginning...
    if (*glob != '^') {
      glob_len += 1;
      if (glob_len > UVM_REGEX_MAX_LENGTH) {
        sprintf(buffer, "uvm_glob_to_re glob expansion exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
        return NULL;
      }
      buffer[iter++] = '^';
    }
    
    // Note that this for loop auto-terminates when '*p' is \0
    for(p = glob; *p; p++) {
      // Replace the glob metacharacters with corresponding regular
      // expression metacharacters.
      switch(*p)
        {
          // '.' Expansion
        case '*':
        case '+':
          glob_len += 2;
          if (glob_len > UVM_REGEX_MAX_LENGTH) {
            sprintf(buffer, "uvm_glob_to_re() expansion exceeds max length(%0d)", UVM_REGEX_MAX_LENGTH);
            return NULL;
          }
          buffer[iter++] = '.';
          buffer[iter++] = *p;
          break;
          
          // Escape Expansion
        case '.':
        case '[':
        case ']':
        case '(':
        case ')':
          glob_len += 2;
          if (glob_len > UVM_REGEX_MAX_LENGTH) {
            sprintf(buffer, "uvm_glob_to_re() expansion exceeds max length(%0d)", UVM_REGEX_MAX_LENGTH);
            return NULL;
          }
          buffer[iter++] = uvm_re_escape_char;
          buffer[iter++] = *p;
          break;
          
          // '?' --> '.'
        case '?':
          buffer[iter++] = '.';
          break;
          
          // Default (copy char)
        default:
          buffer[iter++] = *p;
          break;
        }
    }
    
    
    // Let's check to see if the regular expression is bounded by ^ at
    // the beginning and $ at the end.  If not, add those characters in
    // the appropriate position.
    
    if (buffer[iter-1] != '$') {
      glob_len += 1;
      if (glob_len > UVM_REGEX_MAX_LENGTH) {
        sprintf(buffer, "uvm_glob_to_re glob expansion exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
        return NULL;
      }
      buffer[iter++] = '$';
    }
    
    
    if (with_brackets) {
      glob_len += 1;
      if (glob_len > UVM_REGEX_MAX_LENGTH) {
        sprintf(buffer, "uvm_glob_to_re glob expansion exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
        return NULL;
      }
      buffer[iter++] = uvm_re_bracket_char;
    }
    
    glob_len += 1;
    if (glob_len > UVM_REGEX_MAX_LENGTH) {
      sprintf(buffer, "uvm_glob_to_re glob expansion exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
      return NULL;
    }
    buffer[iter++] = '\0';
    
  }

  // vpi_printf("uvm_re_deglobbed(%s, %0d)\n-->%s\n", glob, with_brackets, buffer);
  return buffer;
}

 
//--------------------------------------------------------------------
// uvm_re_free
//
// Frees a previously compiled regular expression.
//--------------------------------------------------------------------
void uvm_re_free(regex_ptr rexp)
{
  if (rexp != NULL) {
    regfree(rexp);
    free(rexp);
  }
  // vpi_printf("uvm_re_free(%p)\n", rexp);
}

//--------------------------------------------------------------------
// uvm_re_comp
//
// Compiles a regular expression and returns pointer to the compiled
// expression.  A return value of NULL indicates that there was
// an error during compilation, and the error information is available
// via uvm_re_err.
//
// Note that the regular expression is on the heap, and must be freed
// by the caller.
//--------------------------------------------------------------------
regex_ptr uvm_re_comp(const char* re, unsigned char deglob)
{

  // vpi_printf("uvm_re_comp(%s)\n", re); 
  char* buffer = uvm_re_buffer();
  
  // Optionally de-globify regular expression
  const char* deglobbed;
  if (deglob) {
    deglobbed = uvm_re_deglobbed(re, false /* no brackets */);
  } else {
    // No glob, need to copy to buffer manually
    size_t re_len;
    re_len = strlen(re);
    if (re_len > UVM_REGEX_MAX_LENGTH) {
      sprintf(buffer, "uvm_re_comp() re exceeds max length (%0d)", UVM_REGEX_MAX_LENGTH);
      return NULL;
    }
    else {
      // Strip brackets if necessary
      if (re[0] == uvm_re_bracket_char && re[re_len-1] == uvm_re_bracket_char) {
        strncpy(buffer, &re[1], re_len-2);
        buffer[re_len-2] = '\0';
        deglobbed = buffer;
      }
      else {
        deglobbed = re;
      }
    }
  }

  // Safety check.  Args should never be ~null~ since this is called
  // from DPI, but we'll check anyways.
  if (deglobbed == NULL) {
    // uvm_glob_to_re already set the debug buffer
    return NULL;
  }
  // deglobbed is a const pointer to uvm_re_buffer, so never free it.

  regex_ptr rexp;
  rexp = (regex_ptr)malloc(sizeof(regex_t));
  if (rexp == NULL) {
    sprintf(buffer, "uvm_re_comp: internal memory allocation error");
    return NULL;
  }

  int err;
  err = regcomp(rexp, deglobbed, REG_EXTENDED);

  if (err != 0) {
    regerror(err, rexp, buffer, UVM_REGEX_MAX_LENGTH-1);
    uvm_re_free(rexp);
    return NULL;
  }

  // vpi_printf("uvm_re_comp(%s)\n-->%p\n", buffer, rexp); 
  return rexp;
}

//--------------------------------------------------------------------
// uvm_re_exec
//
// Match a string to a pre-compiled regular expression.
//--------------------------------------------------------------------
int uvm_re_exec(regex_ptr rexp, const char * str) {
  // Safety check.
  if (rexp == NULL) {
    sprintf(uvm_re_buffer(), "uvm_re_exec: NULL rexp");
    return REG_NOMATCH;
  }
  if (str == NULL) {
    sprintf(uvm_re_buffer(), "uvm_re_exec: NULL str");
    return REG_NOMATCH;
  }

  int retval;
  retval = regexec(rexp, str, 0, NULL, 0);
  // vpi_printf("uvm_re_exec(%p, %s)\n-->%0d\n", rexp, str, retval);
  return retval;
}

//--------------------------------------------------------------------
// uvm_re_compexec
//
// Compiles a regular expression and executes it in a single operation.
// Reduces the number of necessary language boundary crossings from
// 2 to 1.
//
// Note that the regular expression is on the heap, and must be freed
// by the caller.
//--------------------------------------------------------------------
regex_ptr uvm_re_compexec(const char* re, const char* str, unsigned char deglob, int* exec_ret)
{
  regex_ptr rexp;
  rexp = uvm_re_comp(re, deglob);
  if (rexp != NULL) {
    // Successful compile
    *exec_ret = uvm_re_exec(rexp, str);
  }
  else {
    *exec_ret = REG_NOMATCH;
  }
  // vpi_printf("uvm_re_compexec(%s,%s,%0d)\n-->%p\n", re, str, *exec_ret, rexp);
  return rexp;
}

//--------------------------------------------------------------------
// uvm_re_compexecfree
//
// Compiles a regular expression, executes and frees it in a single operation.
// Reduces the number of necessary language boundary crossings from
// 3 to 1.
//
// Returns 1 on successful execution, 0 on failure.
//--------------------------------------------------------------------
unsigned char uvm_re_compexecfree(const char* re, const char* str, unsigned char deglob, int* exec_ret)
{
  regex_ptr rexp;
  rexp = uvm_re_compexec(re, str, deglob, exec_ret);
  unsigned char success = (rexp != NULL);
  if (success) {
    uvm_re_free(rexp);
  }
  // vpi_printf("uvm_re_compexecfree(%s,%s,%0d)\n-->%0d\n", re, str, *exec_ret, success);
  return success;
}



