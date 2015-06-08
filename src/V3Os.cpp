// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Os-specific function wrapper
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdarg>
#include <sys/stat.h>
#include <sys/types.h>
#include <dirent.h>
#include <unistd.h>
#include <cerrno>
#include <fcntl.h>
#include <iomanip>
#include <memory>

#if defined(WIN32) || defined(__MINGW32__)
# include <direct.h>  // mkdir
#endif

#include "V3Global.h"
#include "V3String.h"
#include "V3Os.h"

//######################################################################
// Environment

string V3Os::getenvStr(const string& envvar, const string& defaultValue) {
    if (const char* envvalue = getenv(envvar.c_str())) {
	return envvalue;
    } else {
	return defaultValue;
    }
}

void V3Os::setenvStr(const string& envvar, const string& value, const string& why) {
    if (why != "") {
	UINFO(1,"export "<<envvar<<"="<<value<<" # "<<why<<endl);
    } else {
	UINFO(1,"export "<<envvar<<"="<<value<<endl);
    }
#if !defined(__MINGW32__) && (defined(_BSD_SOURCE) || (defined(_POSIX_C_SOURCE) && _POSIX_C_SOURCE >= 200112L))
    setenv(envvar.c_str(),value.c_str(),true);
#else
    //setenv() replaced by putenv() in MinGW/Solaris environment. Prototype is different
    //putenv() requires NAME=VALUE format
    string vareq = envvar + "=" + value;
    putenv(const_cast<char*>(vareq.c_str()));
#endif
}

//######################################################################
// Generic filename utilities 

string V3Os::filenameFromDirBase (const string& dir, const string& basename) {
    // Don't return ./{filename} because if filename was absolute, that makes it relative
    if (dir == ".") return basename;
    else return dir+"/"+basename;
}

string V3Os::filenameDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(0,pos);
    } else {
	return ".";
    }
}

string V3Os::filenameNonDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(pos+1);
    } else {
	return filename;
    }
}

string V3Os::filenameNonExt (const string& filename) {
    string base = filenameNonDir(filename);
    string::size_type pos;
    if ((pos = base.find(".")) != string::npos) {
	base.erase(pos);
    }
    return base;
}

string V3Os::filenameSubstitute (const string& filename) {
    string out;
    enum { NONE, PAREN, CURLY } brackets = NONE;
    for (string::size_type pos = 0; pos < filename.length(); ++pos) {
        if ((filename[pos] == '$') && (pos+1 < filename.length())) {
	    switch (filename[pos+1]) {
	        case '{': brackets = CURLY; break;
	        case '(': brackets = PAREN; break;
	        default: brackets = NONE; break;
	    }
	    if (brackets != NONE) pos = pos+1;
	    string::size_type endpos = pos+1;
	    while (((endpos+1) < filename.length()) &&
		   (((brackets==NONE) && (isalnum(filename[endpos+1]) || filename[endpos+1]=='_')) ||
		    ((brackets==CURLY) && (filename[endpos+1]!='}')) ||
		    ((brackets==PAREN) && (filename[endpos+1]!=')'))))
		++endpos;
	    // Catch bracket errors
	    if (((brackets==CURLY) && (filename[endpos+1]!='}')) ||
		((brackets==PAREN) && (filename[endpos+1]!=')'))) {
	      v3fatal("Unmatched brackets in variable substitution in file: "+filename);
	    }
	    string envvar = filename.substr(pos+1,endpos-pos);
	    const char* envvalue = NULL;
	    if (envvar != "") envvalue = getenv(envvar.c_str());
	    if (envvalue) {
		out += envvalue;
		if (brackets==NONE) pos = endpos;
		else pos = endpos+1;
	    } else {
		out += filename[pos];  // *pos == '$'
	    }
	} else {
	    out += filename[pos];
	}
    }
    return out;

}

bool V3Os::filenameIsRel(const string& filename) {
    return (filename.length()>0 && filename[0] != '/');
}

//######################################################################
// Directory utilities

void V3Os::createDir(const string& dirname) {
#if defined(_WIN32) || defined(__MINGW32__)
    mkdir(dirname.c_str());
#else
    mkdir(dirname.c_str(), 0777);
#endif
}

void V3Os::unlinkRegexp(const string& dir, const string& regexp) {
    if (DIR* dirp = opendir(dir.c_str())) {
	while (struct dirent* direntp = readdir(dirp)) {
	    if (VString::wildmatch(direntp->d_name, regexp.c_str())) {
		string fullname = dir + "/" + string(direntp->d_name);
		unlink (fullname.c_str());
	    }
	}
	closedir(dirp);
    }
}
