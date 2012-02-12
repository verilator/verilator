//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
#include <sys/types.h>
#include <sys/stat.h>
#ifndef _WIN32
# include <sys/utsname.h>
#endif
#include <cctype>
#include <dirent.h>
#include <unistd.h>
#include <set>
#include <list>
#include <map>
#include <memory>

#include "V3Global.h"
#include "V3Options.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3PreShell.h"

#include "config_rev.h"

//######################################################################
// V3 Internal state

struct V3OptionsImp {
    // TYPES
    typedef std::map<string,set<string> > DirMap;	// Directory listing

    // STATE
    list<string>	m_allArgs;	// List of every argument encountered
    list<string>	m_incDirUsers;		// Include directories (ordered)
    set<string>		m_incDirUserSet;	// Include directories (for removing duplicates)
    list<string>	m_incDirFallbacks;	// Include directories (ordered)
    set<string>		m_incDirFallbackSet;	// Include directories (for removing duplicates)
    list<string>	m_libExtVs;	// Library extensions (ordered)
    set<string>		m_libExtVSet;	// Library extensions (for removing duplicates)
    DirMap		m_dirMap;	// Directory listing

    // ACCESSOR METHODS
    void addIncDirUser(const string& incdir) {
	if (m_incDirUserSet.find(incdir) == m_incDirUserSet.end()) {
	    m_incDirUserSet.insert(incdir);
	    m_incDirUsers.push_back(incdir);
	    m_incDirFallbacks.remove(incdir);  // User has priority over Fallback
	    m_incDirFallbackSet.erase(incdir);  // User has priority over Fallback
	}
    }
    void addIncDirFallback(const string& incdir) {
	if (m_incDirUserSet.find(incdir) == m_incDirUserSet.end()) {  // User has priority over Fallback
	    if (m_incDirFallbackSet.find(incdir) == m_incDirFallbackSet.end()) {
		m_incDirFallbackSet.insert(incdir);
		m_incDirFallbacks.push_back(incdir);
	    }
	}
    }
    void addLibExtV(const string& libext) {
	if (m_libExtVSet.find(libext) == m_libExtVSet.end()) {
	    m_libExtVSet.insert(libext);
	    m_libExtVs.push_back(libext);
	}
    }
    V3OptionsImp() {}
};

void V3Options::addIncDirUser(const string& incdir) {
    m_impp->addIncDirUser(incdir);
}
void V3Options::addIncDirFallback(const string& incdir) {
    m_impp->addIncDirFallback(incdir);
}
void V3Options::addLibExtV(const string& libext) {
    m_impp->addLibExtV(libext);
}
void V3Options::addDefine(const string& defline) {
    // Split +define+foo=value into the appropriate parts and parse
    string def = defline;
    string value;
    string::size_type pos;
    if ( ((pos=defline.find("+")) != string::npos)
	 || ((pos=defline.find("=")) != string::npos)) {
	value = def.substr(pos+1);
	def.erase(pos);
    }
    V3PreShell::defineCmdLine(def,value);
}

void V3Options::addCppFile(const string& filename) {
    if (m_cppFiles.find(filename) == m_cppFiles.end()) {
	m_cppFiles.insert(filename);
    }
}
void V3Options::addCFlags(const string& filename) {
    if (m_cFlags.find(filename) == m_cFlags.end()) {
	m_cFlags.insert(filename);
    }
}
void V3Options::addLdLibs(const string& filename) {
    if (m_ldLibs.find(filename) == m_ldLibs.end()) {
	m_ldLibs.insert(filename);
    }
}
void V3Options::addFuture(const string& flag) {
    if (m_futures.find(flag) == m_futures.end()) {
	m_futures.insert(flag);
    }
}
bool V3Options::isFuture(const string& flag) const {
    return m_futures.find(flag) != m_futures.end();
}
bool V3Options::isLibraryFile(const string& filename) const {
    return m_libraryFiles.find(filename) != m_libraryFiles.end();
}

void V3Options::addLibraryFile(const string& filename) {
    if (m_libraryFiles.find(filename) == m_libraryFiles.end()) {
	m_libraryFiles.insert(filename);
    }
}
void V3Options::addVFile(const string& filename) {
    // We use a list for v files, because it's legal to have includes
    // in a specific order and multiple of them.
    m_vFiles.push_back(filename);
}
void V3Options::addArg(const string& arg) {
    m_impp->m_allArgs.push_back(arg);
}

string V3Options::allArgsString() {
    string out;
    for (list<string>::iterator it=m_impp->m_allArgs.begin(); it!=m_impp->m_allArgs.end(); ++it) {
	if (out != "") out += " ";
	out += *it;
    }
    return out;
}

//######################################################################
// Language class

V3LangCode::V3LangCode (const char* textp) {
    // Return code for given string, or ERROR, which is a bad code
    for (int codei=V3LangCode::L_ERROR; codei<V3LangCode::_ENUM_END; ++codei) {
	V3LangCode code = (V3LangCode)codei;
	if (0==strcasecmp(textp,code.ascii())) {
	    m_e = code; return;
	}
    }
    m_e = V3LangCode::L_ERROR;
}

//######################################################################
// File searching

string V3Options::filenameFromDirBase (const string& dir, const string& basename) {
    // Don't return ./{filename} because if filename was absolute, that makes it relative
    if (dir == ".") return basename;
    else return dir+"/"+basename;
}

string V3Options::filenameDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(0,pos);
    } else {
	return ".";
    }
}

string V3Options::filenameNonDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(pos+1);
    } else {
	return filename;
    }
}

string V3Options::filenameNonExt (const string& filename) {
    string base = filenameNonDir(filename);
    string::size_type pos;
    if ((pos = base.find(".")) != string::npos) {
	base.erase(pos);
    }
    return base;
}

string V3Options::filenameSubstitute (const string& filename) {
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

bool V3Options::filenameIsRel(const string& filename) {
    return (filename.length()>0 && filename[0] != '/');
}

bool V3Options::fileStatDir(const string& filename) {
    struct stat	m_stat;		// Stat information
    int err = stat(filename.c_str(), &m_stat);
    if (err!=0) return false;
    if (!S_ISDIR(m_stat.st_mode)) return false;
    return true;
}

bool V3Options::fileStatNormal(const string& filename) {
    struct stat	m_stat;		// Stat information
    int err = stat(filename.c_str(), &m_stat);
    if (err!=0) return false;
    if (S_ISDIR(m_stat.st_mode)) return false;
    return true;
}

string V3Options::fileExists (const string& filename) {
    // Surprisingly, for VCS and other simulators, this process
    // is quite slow; presumably because of re-reading each directory
    // many times.  So we read a whole dir at once and cache it

    string dir = filenameDir(filename);
    string basename = filenameNonDir(filename);

    V3OptionsImp::DirMap::iterator diriter = m_impp->m_dirMap.find(dir);
    if (diriter == m_impp->m_dirMap.end()) {
	// Read the listing
	m_impp->m_dirMap.insert(make_pair(dir, set<string>() ));
	diriter = m_impp->m_dirMap.find(dir);

	set<string>* setp = &(diriter->second);

	if (DIR* dirp = opendir(dir.c_str())) {
	    while (struct dirent* direntp = readdir(dirp)) {

		setp->insert(direntp->d_name);
	    }
	    closedir(dirp);
	}
    }
    // Find it
    set<string>* filesetp = &(diriter->second);
    set<string>::iterator fileiter = filesetp->find(basename);
    if (fileiter == filesetp->end()) {
	return "";  // Not found
    }
    // Check if it is a directory, ignore if so
    string filenameOut = filenameFromDirBase (dir, basename);
    if (!fileStatNormal(filenameOut)) return "";   // Directory
    return filenameOut;
}

string V3Options::filePathCheckOneDir(const string& modname, const string& dirname) {
    for (list<string>::iterator extIter=m_impp->m_libExtVs.begin(); extIter!=m_impp->m_libExtVs.end(); ++extIter) {
	string fn = filenameFromDirBase(dirname, modname+*extIter);
	string exists = fileExists(fn);
	if (exists!="") {
	    // Strip ./, it just looks ugly
	    if (exists.substr(0,2)=="./") exists.erase(0,2);
	    return exists;
	}
    }
    return "";
}

string V3Options::filePath (FileLine* fl, const string& modname,
			    const string& errmsg) {   // Error prefix or "" to suppress error
    // Find a filename to read the specified module name,
    // using the incdir and libext's.
    // Return "" if not found.
    for (list<string>::iterator dirIter=m_impp->m_incDirUsers.begin();
	 dirIter!=m_impp->m_incDirUsers.end(); ++dirIter) {
	string exists = filePathCheckOneDir(modname, *dirIter);
	if (exists!="") return exists;
    }
    for (list<string>::iterator dirIter=m_impp->m_incDirFallbacks.begin();
	 dirIter!=m_impp->m_incDirFallbacks.end(); ++dirIter) {
	string exists = filePathCheckOneDir(modname, *dirIter);
	if (exists!="") return exists;
    }

    // Warn and return not found
    if (errmsg != "") {
	fl->v3error(errmsg+modname);
	filePathLookedMsg(fl, modname);
    }
    return "";
}

void V3Options::filePathLookedMsg(FileLine* fl, const string& modname) {
    static bool shown_notfound_msg = false;
    if (!shown_notfound_msg) {
	shown_notfound_msg = true;
	if (m_impp->m_incDirUsers.empty()) {
	    fl->v3error("This may be because there's no search path specified with -I<dir>."<<endl);
	}
	fl->v3error("Looked in:"<<endl);
	for (list<string>::iterator dirIter=m_impp->m_incDirUsers.begin();
	     dirIter!=m_impp->m_incDirUsers.end(); ++dirIter) {
	    for (list<string>::iterator extIter=m_impp->m_libExtVs.begin(); extIter!=m_impp->m_libExtVs.end(); ++extIter) {
		string fn = filenameFromDirBase(*dirIter,modname+*extIter);
		fl->v3error("      "<<fn<<endl);
	    }
	}
	for (list<string>::iterator dirIter=m_impp->m_incDirFallbacks.begin();
	     dirIter!=m_impp->m_incDirFallbacks.end(); ++dirIter) {
	    for (list<string>::iterator extIter=m_impp->m_libExtVs.begin(); extIter!=m_impp->m_libExtVs.end(); ++extIter) {
		string fn = filenameFromDirBase(*dirIter,modname+*extIter);
		fl->v3error("      "<<fn<<endl);
	    }
	}
    }
}

void V3Options::unlinkRegexp(const string& dir, const string& regexp) {
    if (DIR* dirp = opendir(dir.c_str())) {
	while (struct dirent* direntp = readdir(dirp)) {
	    if (wildmatch(direntp->d_name, regexp.c_str())) {
		string fullname = dir + "/" + string(direntp->d_name);
		unlink (fullname.c_str());
	    }
	}
	closedir(dirp);
    }
}

//######################################################################
// Environment

string V3Options::getenvStr(const string& envvar, const string& defaultValue) {
    if (const char* envvalue = getenv(envvar.c_str())) {
	return envvalue;
    } else {
	return defaultValue;
    }
}

void V3Options::setenvStr(const string& envvar, const string& value, const string& why) {
    if (why != "") {
	UINFO(1,"export "<<envvar<<"="<<value<<" # "<<why<<endl);
    } else {
	UINFO(1,"export "<<envvar<<"="<<value<<endl);
    }
#ifndef _WIN32
    setenv(envvar.c_str(),value.c_str(),true);
#else
    //setenv() replaced by putenv() in MinGW environment. Prototype is different
    //putenv() requires NAME=VALUE format
    string vareq = envvar + "=" + value;
    putenv(vareq.c_str());
#endif
}

string V3Options::getenvPERL() {
    return getenvStr("PERL","perl");
}

string V3Options::getenvSYSTEMC() {
    string var = getenvStr("SYSTEMC","");
    if (var == "" && string(DEFENV_SYSTEMC) != "") {
	var = DEFENV_SYSTEMC;
	setenvStr("SYSTEMC", var, "Hardcoded at build time");
    }
    return var;
}

string V3Options::getenvSYSTEMC_ARCH() {
    string var = getenvStr("SYSTEMC_ARCH","");
    if (var == "" && string(DEFENV_SYSTEMC_ARCH) != "") {
	var = DEFENV_SYSTEMC_ARCH;
	setenvStr("SYSTEMC_ARCH", var, "Hardcoded at build time");
    }
    if (var == "") {
#if defined (__MINGW32__)
        // Hardcoded with MINGW current version. Would like a better way.
        string sysname = "MINGW32_NT-5.0";
        var = "mingw32";
#elif defined (_WIN32)
        string sysname = "WIN32";
        var = "win32";
#else
	struct utsname uts;
	uname(&uts);
	string sysname = downcase(uts.sysname);  // aka  'uname -s'
	if (wildmatch(sysname.c_str(), "*solaris*")) { var = "gccsparcOS5"; }
	else if (wildmatch(sysname.c_str(), "*cygwin*")) { var ="cygwin"; }
	else { var = "linux"; }
#endif
	setenvStr("SYSTEMC_ARCH", var,"From sysname '"+sysname+"'");
    }
    return var;
}

string V3Options::getenvSYSTEMC_INCLUDE() {
    string var = getenvStr("SYSTEMC_INCLUDE","");
    if (var == "" && string(DEFENV_SYSTEMC_INCLUDE) != "") {
	var = DEFENV_SYSTEMC_INCLUDE;
	setenvStr("SYSTEMC_INCLUDE", var, "Hardcoded at build time");
    }
    if (var == "") {
	string sc = getenvSYSTEMC();
	if (sc != "") var = sc+"/include";
    }
    // Only correct or check it if we really need the value
    if (v3Global.opt.usingSystemCLibs()) {
	if (var == "") {
	    v3fatal("Need $SYSTEMC_INCLUDE in environment or when Verilator configured\n"
		    "Probably System-C isn't installed, see http://www.systemc.org\n");
	}
    }
    return var;
}

string V3Options::getenvSYSTEMC_LIBDIR() {
    string var = getenvStr("SYSTEMC_LIBDIR","");
    if (var == "" && string(DEFENV_SYSTEMC_LIBDIR) != "") {
	var = DEFENV_SYSTEMC_LIBDIR;
	setenvStr("SYSTEMC_LIBDIR", var, "Hardcoded at build time");
    }
    if (var == "") {
	string sc = getenvSYSTEMC();
	string arch = getenvSYSTEMC_ARCH();
	if (sc != "" && arch != "") var = sc+"/lib-"+arch;
    }
    // Only correct or check it if we really need the value
    if (v3Global.opt.usingSystemCLibs()) {
	if (var == "") {
	    v3fatal("Need $SYSTEMC_LIBDIR in environment or when Verilator configured\n"
		    "Probably System-C isn't installed, see http://www.systemc.org\n");
	}
    }
    return var;
}

string V3Options::getenvSYSTEMPERL() {
    // Must be careful to set SYSTEMPERL_INCLUDE first else we'd setenv
    // SYSTEMPERL which would override a DEFENVed SYSTEMPERL_INCLUDE.
    V3Options::getenvSYSTEMPERL_INCLUDE();
    return V3Options::getenvSYSTEMPERLGuts();
}

string V3Options::getenvSYSTEMPERLGuts() {
    // Get SYSTEMPERL when SYSTEMPERL_INCLUDE has already been tested
    string var = getenvStr("SYSTEMPERL","");
    if (var == "" && string(DEFENV_SYSTEMPERL) != "") {
	var = DEFENV_SYSTEMPERL;
	setenvStr("SYSTEMPERL", var, "Hardcoded at build time");
    }
    return var;
}

string V3Options::getenvSYSTEMPERL_INCLUDE() {
    string var = getenvStr("SYSTEMPERL_INCLUDE","");
    if (var == "") {
	string sp_src = V3Options::getenvSYSTEMPERLGuts()+"/src";
	if (V3Options::fileStatNormal(sp_src+"/systemperl.h")) {
 	    var = sp_src;
	    setenvStr ("SYSTEMPERL_INCLUDE", var, "From $SYSTEMPERL/src");
	} else if (string(DEFENV_SYSTEMPERL_INCLUDE) != "") {
	    // Note if SYSTEMPERL is DEFENVed, then SYSTEMPERL_INCLUDE is also DEFENVed
	    // So we don't need to sweat testing DEFENV_SYSTEMPERL also
	    var = DEFENV_SYSTEMPERL_INCLUDE;
	    setenvStr("SYSTEMPERL_INCLUDE", var, "Hardcoded at build time");
	}
    }
    // Only correct or check it if we really need the value
    if (v3Global.opt.usingSystemPerlLibs()) {
	// We warn about $SYSTEMPERL instead of _INCLUDE since that's more likely
	// what users will want to set.
	if (var == "") {
	    v3fatal("Need $SYSTEMPERL and $SYSTEMPERL_INCLUDE in environment for --sp or --coverage\n"
		    "Probably System-Perl isn't installed, see http://www.veripool.org/systemperl\n");
	}
	else if (var != "" && !V3Options::fileStatNormal(var+"/systemperl.h")) {
	    v3fatal("Neither $SYSTEMPERL nor $SYSTEMPERL_INCLUDE environment vars to point to System-Perl kit: "<<var<<endl);
	}
    }
    return var;
}

string V3Options::getenvVERILATOR_ROOT() {
    string var = getenvStr("VERILATOR_ROOT","");
    if (var == "" && string(DEFENV_VERILATOR_ROOT) != "") {
	var = DEFENV_VERILATOR_ROOT;
	setenvStr("VERILATOR_ROOT", var.c_str(), "Hardcoded at build time");
    }
    if (var == "") {
	v3fatal("$VERILATOR_ROOT needs to be in environment\n");
    }
    return var;
}

//######################################################################
// Wildcard

// Double procedures, inlined, unrolls loop much better
inline bool V3Options::wildmatchi(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
	    while (wildmatch(s, p) == false)
		if (*++s == '\0')
		    return false;
	    return true;
	}
    }
    return (*s == '\0');
}

bool V3Options::wildmatch(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
	    while (wildmatchi(s, p) == false)
		if (*++s == '\0')
		    return false;
	    return true;
	}
    }
    return (*s == '\0');
}

string V3Options::downcase(const string& str) {
    string out = str;
    for (string::iterator pos = out.begin(); pos != out.end(); ++pos) {
	*pos = tolower(*pos);
    }
    return out;
}

//######################################################################
// V3 Options accessors

string V3Options::version() {
    string ver = DTVERSION;
    ver += " rev "+cvtToStr(DTVERSION_rev);
#ifdef NEW_ORDERING
    ver += " (ord)";
#endif
    return ver;
}

void V3Options::throwSigsegv() {
    // cppcheck-suppress nullPointer
    char* zp=NULL; *zp=0;    
}

//######################################################################
// V3 Options utilities

string V3Options::argString (int argc, char** argv) {
    // Return list of arguments as simple string
    string opts;
    for (int i=0; i<argc; ++i)  {
	if (i!=0) opts += " ";
	opts += string(argv[i]);
    }
    return opts;
}

//######################################################################
// V3 Options Parsing

void V3Options::parseOpts (FileLine* fl, int argc, char** argv) {
    // Parse all options
    // Inital entry point from Verilator.cpp
    parseOptsList (fl, ".", argc, argv);

    // Default certain options and error check
    // Detailed error, since this is what we often get when run with minimal arguments
    if (vFiles().empty()) {
	v3fatal("verilator: No Input Verilog file specified on command line, see verilator --help for more information\n");
    }

    // Default prefix to the filename
    if (prefix()=="" && topModule()!="") m_prefix = string("V")+topModule();
    if (prefix()=="") m_prefix = string("V")+filenameNonExt(*(vFiles().begin()));
    if (modPrefix()=="") m_modPrefix = prefix();

    // Find files in makedir
    addIncDirFallback(makeDir());
}

//======================================================================

bool V3Options::onoff(const char* sw, const char* arg, bool& flag) {
    // if sw==arg, then return true (found it), and flag=true
    // if sw=="-no-arg", then return true (found it), and flag=false
    // if sw=="-noarg", then return true (found it), and flag=false
    // else return false
    if (arg[0]!='-') v3fatalSrc("OnOff switches must have leading dash.\n");
    if (0==strcmp(sw,arg)) { flag=true; return true; }
    else if (0==strncmp(sw,"-no",3) && (0==strcmp(sw+3,arg+1))) { flag=false; return true; }
    else if (0==strncmp(sw,"-no-",4) && (0==strcmp(sw+4,arg+1))) { flag=false; return true; }
    return false;
}

bool V3Options::suffixed(const char* sw, const char* arg) {
    if (strlen(arg) > strlen(sw)) return false;
    return (0==strcmp(sw+strlen(sw)-strlen(arg), arg));
}

void V3Options::parseOptsList(FileLine* fl, const string& optdir, int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
    for (int i=0; i<argc; ++i)  {
	addArg(argv[i]);	// -f's really should be inserted in the middle, but this is for debug
    }
#define shift { ++i; }
    for (int i=0; i<argc; )  {
	UINFO(9, " Option: "<<argv[i]<<endl);
	if (argv[i][0]=='+') {
	    char *sw = argv[i];
	    if ( !strncmp (sw, "+define+", 8)) {
		addDefine (string (sw+strlen("+define+")));
	    }
	    else if ( !strncmp (sw, "+incdir+", 8)) {
		addIncDirUser (parseFileArg(optdir, string (sw+strlen("+incdir+"))));
	    }
	    else if ( !strncmp (sw, "+libext+", 8)) {
		string exts = string(sw+strlen("+libext+"));
		string::size_type pos;
		while ((pos=exts.find("+")) != string::npos) {
		    addLibExtV (exts.substr(0,pos));
		    exts = exts.substr(pos+1);
		}
		addLibExtV (exts);
	    }
	    else if ( !strcmp (sw, "+librescan")) { // NOP
	    }
	    else if ( !strcmp (sw, "+notimingchecks")) { // NOP
	    }
	    else {
		fl->v3fatal ("Invalid Option: "<<argv[i]);
	    }
	    shift;
	} // + options
	else if (argv[i][0]=='-') {
	    const char *sw = argv[i];
	    bool flag = true;
	    // Allow gnu -- switches
	    if (sw[0]=='-' && sw[1]=='-') ++sw;
	    if (0) {}
	    // Single switches
	    else if ( !strcmp (sw, "-E") )			{ m_preprocOnly = true; }
	    else if ( onoff   (sw, "-MMD", flag/*ref*/) )	{ m_makeDepend = flag; }
	    else if ( onoff   (sw, "-MP", flag/*ref*/) )	{ m_makePhony = flag; }
	    else if ( onoff   (sw, "-assert", flag/*ref*/) )	{ m_assert = flag; m_psl = flag; }
	    else if ( onoff   (sw, "-autoflush", flag/*ref*/) )	{ m_autoflush = flag; }
	    else if ( onoff   (sw, "-bbox-sys", flag/*ref*/) )	{ m_bboxSys = flag; }
	    else if ( onoff   (sw, "-bbox-unsup", flag/*ref*/) ) { m_bboxUnsup = flag; }
	    else if ( !strcmp (sw, "-cc") )			{ m_outFormatOk = true; m_systemC = false; m_systemPerl = false; }
	    else if ( onoff   (sw, "-cdc", flag/*ref*/) )	{ m_cdc = flag; }
	    else if ( onoff   (sw, "-coverage", flag/*ref*/) )	{ coverage(flag); }
	    else if ( onoff   (sw, "-coverage-line", flag/*ref*/) ){ m_coverageLine = flag; }
	    else if ( onoff   (sw, "-coverage-toggle", flag/*ref*/) ){ m_coverageToggle = flag; }
	    else if ( onoff   (sw, "-coverage-underscore", flag/*ref*/) ){ m_coverageUnderscore = flag; }
	    else if ( onoff   (sw, "-coverage-user", flag/*ref*/) ){ m_coverageUser = flag; }
	    else if ( onoff   (sw, "-covsp", flag/*ref*/) )	{ }  // TBD
	    else if ( !strcmp (sw, "-debug-abort") )		{ abort(); } // Undocumented, see also --debug-sigsegv
	    else if ( onoff   (sw, "-debug-check", flag/*ref*/) ){ m_debugCheck = flag; }
	    else if ( !strcmp (sw, "-debug-sigsegv") )		{ throwSigsegv(); }  // Undocumented, see also --debug-abort
	    else if ( !strcmp (sw, "-debug-fatalsrc") )		{ v3fatalSrc("--debug-fatal-src"); }  // Undocumented, see also --debug-abort
	    else if ( onoff   (sw, "-dump-tree", flag/*ref*/) )	{ m_dumpTree = flag; }
	    else if ( onoff   (sw, "-exe", flag/*ref*/) )	{ m_exe = flag; }
	    else if ( onoff   (sw, "-ignc", flag/*ref*/) )	{ m_ignc = flag; }
	    else if ( onoff   (sw, "-inhibit-sim", flag/*ref*/)){ m_inhibitSim = flag; }
	    else if ( onoff   (sw, "-l2name", flag/*ref*/) )	{ m_l2Name = flag; }
	    else if ( onoff   (sw, "-lint-only", flag/*ref*/) )	{ m_lintOnly = flag; }
	    else if ( !strcmp (sw, "-no-pins64") )		{ m_pinsBv = 33; }
	    else if ( !strcmp (sw, "-pins64") )			{ m_pinsBv = 65; }
	    else if ( onoff   (sw, "-pins-uint8", flag/*ref*/) ){ m_pinsUint8 = flag; }
	    else if ( !strcmp (sw, "-private") )		{ m_public = false; }
	    else if ( onoff   (sw, "-profile-cfuncs", flag/*ref*/) )	{ m_profileCFuncs = flag; }
	    else if ( onoff   (sw, "-psl", flag/*ref*/) )		{ m_psl = flag; }
	    else if ( onoff   (sw, "-public", flag/*ref*/) )		{ m_public = flag; }
	    else if ( !strcmp (sw, "-sc") )				{ m_outFormatOk = true; m_systemC = true; m_systemPerl = false; }
	    else if ( onoff   (sw, "-skip-identical", flag/*ref*/) )	{ m_skipIdentical = flag; }
	    else if ( !strcmp (sw, "-sp") )				{ m_outFormatOk = true; m_systemC = true; m_systemPerl = true; }
	    else if ( onoff   (sw, "-stats", flag/*ref*/) )		{ m_stats = flag; }
	    else if ( !strcmp (sw, "-sv") )				{ m_language = V3LangCode::L1800_2005; }
	    else if ( onoff   (sw, "-trace", flag/*ref*/) )		{ m_trace = flag; }
	    else if ( onoff   (sw, "-trace-dups", flag/*ref*/) )	{ m_traceDups = flag; }
	    else if ( onoff   (sw, "-trace-underscore", flag/*ref*/) )	{ m_traceUnderscore = flag; }
	    else if ( onoff   (sw, "-underline-zero", flag/*ref*/) )	{ m_underlineZero = flag; }  // Undocumented, old Verilator-2
	    // Optimization
	    else if ( !strncmp (sw, "-O", 2) ) {
		for (const char* cp=sw+strlen("-O"); *cp; ++cp) {
		    flag = isupper(*cp);
		    switch (tolower(*cp)) {
		    case '0': optimize(0); break; // 0=all off
		    case '1': optimize(1); break; // 1=all on
		    case '2': optimize(2); break; // 2=not used
		    case '3': optimize(3); break; // 3=high
		    case 'a': m_oTable = flag; break;
		    case 'b': m_oCombine = flag; break;
		    case 'c': m_oConst = flag; break;
		    case 'e': m_oCase = flag; break;
		    case 'f': m_oFlopGater = flag; break;
		    case 'g': m_oGate = flag; break;
		    case 'i': m_oInline = flag; break;
		    case 'k': m_oSubstConst = flag; break;
		    case 'l': m_oLife = flag; break;
		    case 'p': m_public = !flag; break;  //With -Op so flag=0, we want public on so few optimizations done
		    case 'r': m_oReorder = flag; break;
		    case 's': m_oSplit = flag; break;
		    case 't': m_oLifePost = flag; break;
		    case 'u': m_oSubst = flag; break;
		    case 'x': m_oExpand = flag; break;
		    case 'y': m_oAcycSimp = flag; break;
		    case 'z': m_oLocalize = flag; break;
		    default:  break; // No error, just ignore
		    }
		}
	    }
	    // Parameterized switches
	    else if ( !strcmp (sw, "-CFLAGS") && (i+1)<argc ) {
		shift;
		addCFlags(argv[i]);
	    }
	    else if ( !strncmp (sw, "-D", 2)) {
		addDefine (string (sw+strlen("-D")));
	    }
	    else if ( !strcmp (sw, "-debug") ) {
		setDebugMode(3);
	    }
	    else if ( !strcmp (sw, "-debugi") && (i+1)<argc ) {
		shift;
		setDebugMode(atoi(argv[i]));
	    }
	    else if ( !strncmp (sw, "-debugi-", strlen("-debugi-"))) {
		const char* src = sw+strlen("-debugi-");
		shift;
		setDebugSrcLevel(src, atoi(argv[i]));
	    }
	    else if ( !strcmp (sw, "-error-limit") && (i+1)<argc ) {
		shift;
		m_errorLimit = atoi(argv[i]);
	    }
	    else if ( !strncmp (sw, "-I", 2)) {
		addIncDirUser (parseFileArg(optdir, string (sw+strlen("-I"))));
	    }
	    else if ( !strcmp (sw, "-if-depth") && (i+1)<argc ) {
		shift;
		m_ifDepth = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-inline-mult") && (i+1)<argc ) {
		shift;
		m_inlineMult = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-LDFLAGS") && (i+1)<argc ) {
		shift;
		addLdLibs(argv[i]);
	    }
	    else if ( !strcmp (sw, "-language") && (i+1)<argc ) {
		shift;
		V3LangCode optval = V3LangCode(argv[i]);
		if (optval.legal()) {
		    m_language = optval;
		} else {
		    fl->v3fatal("Unknown language specified: "<<argv[i]);
		}
	    }
	    else if ( !strcmp (sw, "-Mdir") && (i+1)<argc ) {
		shift; m_makeDir = argv[i];
		addIncDirFallback (string (m_makeDir));	 // Need to find generated files there too
	    }
	    else if ( !strcmp (sw, "-o") && (i+1)<argc ) {
		shift; m_exeName = argv[i];
	    }
	    else if ( !strcmp (sw, "-output-split") && (i+1)<argc ) {
		shift;
		m_outputSplit = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-output-split-cfuncs") && (i+1)<argc ) {
		shift;
		m_outputSplitCFuncs = atoi(argv[i]);
		if (m_outputSplitCFuncs && (!m_outputSplitCTrace
					    || m_outputSplitCTrace>m_outputSplitCFuncs)) {
		    m_outputSplitCTrace = m_outputSplitCFuncs;
		}
	    }
	    else if ( !strcmp (sw, "-output-split-ctrace") ) { // Undocumented optimization tweak
		shift;
		m_outputSplitCTrace = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-trace-depth") && (i+1)<argc ) {
		shift;
		m_traceDepth = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-trace-max-array") && (i+1)<argc ) {
		shift;
		m_traceMaxArray = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-trace-max-width") && (i+1)<argc ) {
		shift;
		m_traceMaxWidth = atoi(argv[i]);
	    }
	    else if ( !strncmp (sw, "-U", 2)) {
		V3PreShell::undef (string (sw+strlen("-U")));
	    }
	    else if ( !strcmp (sw, "-unroll-count") ) { // Undocumented optimization tweak
		shift;
		m_unrollCount = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-unroll-stmts") ) {	// Undocumented optimization tweak
		shift;
		m_unrollStmts = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-v") && (i+1)<argc ) {
		shift;
		V3Options::addLibraryFile(parseFileArg(optdir,argv[i]));
	    }
	    else if ( !strcmp (sw, "-V") ) {
		showVersion(true);
		exit(0);
	    }
	    else if ( !strcmp (sw, "-version") ) {
		showVersion(false);
		exit(0);
	    }
	    else if ( !strcmp (sw, "-Wall") )	{
		FileLine::globalWarnLintOff(false);
		FileLine::globalWarnStyleOff(false);
	    }
	    else if ( !strncmp (sw, "-Werror-",strlen("-Werror-")) )	{
		string msg = sw+strlen("-Werror-");
		V3ErrorCode code (msg.c_str());
		if (code == V3ErrorCode::EC_ERROR) {
		    if (!isFuture(msg)) {
			fl->v3fatal("Unknown warning specified: "<<sw);
		    }
		} else {
		    V3Error::pretendError(code, true);
		}
	    }
	    else if ( !strncmp (sw, "-Wfuture-",strlen("-Wfuture-")) )	{
		string msg = sw+strlen("-Wfuture-");
		// Note it may not be a future option, but one that is currently implemented.
		addFuture(msg);
	    }
	    else if ( !strncmp (sw, "-Wno-",5) )	{
		if (!strcmp (sw, "-Wno-lint")) {
		    FileLine::globalWarnLintOff(true);
		    FileLine::globalWarnStyleOff(true);
		}
		else if (!strcmp (sw, "-Wno-style")) {
		    FileLine::globalWarnStyleOff(true);
		}
		else if (!strcmp (sw, "-Wno-fatal")) {
		    m_warnFatal = false;
		}
		else {
		    string msg = sw+strlen("-Wno-");
		    if (!(FileLine::globalWarnOff(msg, true))) {
			fl->v3fatal("Unknown warning specified: "<<sw);
		    }
		}
	    }
	    else if ( !strncmp (sw, "-Wwarn-",5) )	{
		if (!strcmp (sw, "-Wwarn-lint")) {
		    FileLine::globalWarnLintOff(false);
		}
		else if (!strcmp (sw, "-Wwarn-style")) {
		    FileLine::globalWarnStyleOff(false);
		}
		else {
		    string msg = sw+strlen("-Wwarn-");
		    if (!(FileLine::globalWarnOff(msg, false))) {
			fl->v3fatal("Unknown warning specified: "<<sw);
		    }
		}
	    }
	    else if ( !strcmp (sw, "-bin") && (i+1)<argc ) {
		shift; m_bin = argv[i];
	    }
	    else if ( !strcmp (sw, "-compiler") && (i+1)<argc) {
		shift;
		if (!strcmp (argv[i], "gcc")) {
		    m_compLimitParens = 0;
		} else if (!strcmp (argv[i], "msvc")) {
		    m_compLimitParens = 80;   // 128, but allow some room
		    m_compLimitBlocks = 80;   // 128, but allow some room
		} else {
		    fl->v3fatal("Unknown setting for --compiler: "<<argv[i]);
		}
	    }
	    else if ( !strcmp (sw, "-F") && (i+1)<argc ) {
		shift;
		parseOptsFile(fl, parseFileArg(optdir,argv[i]), true);
	    }
	    else if ( !strcmp (sw, "-f") && (i+1)<argc ) {
		shift;
		parseOptsFile(fl, parseFileArg(optdir,argv[i]), false);
	    }
	    else if ( !strcmp (sw, "-gdb") && (i+1)<argc ) {
		shift; // Used only in perl shell
	    }
	    else if ( !strcmp (sw, "-gdbbt")) {
		// Used only in perl shell
	    }
	    else if ( !strcmp (sw, "-mod-prefix") && (i+1)<argc ) {
		shift; m_modPrefix = argv[i];
	    }
	    else if ( !strcmp (sw, "-pins-bv") && (i+1)<argc ) {
		shift; m_pinsBv = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-pipe-filter") && (i+1)<argc ) {
		shift; m_pipeFilter = argv[i];
	    }
	    else if ( !strcmp (sw, "-prefix") && (i+1)<argc ) {
		shift; m_prefix = argv[i];
		if (m_modPrefix=="") m_modPrefix = m_prefix;
	    }
	    else if ( !strcmp (sw, "-top-module") && (i+1)<argc ) {
		shift; m_topModule = argv[i];
	    }
	    else if ( !strcmp (sw, "-unused-regexp") && (i+1)<argc ) {
		shift; m_unusedRegexp = argv[i];
	    }
	    else if ( !strcmp (sw, "-x-assign") && (i+1)<argc) {
		shift;
		if (!strcmp (argv[i], "0")) { m_xAssign="0"; }
		else if (!strcmp (argv[i], "1")) { m_xAssign="1"; }
		else if (!strcmp (argv[i], "fast")) { m_xAssign="fast"; }
		else if (!strcmp (argv[i], "unique")) { m_xAssign="unique"; }
		else {
		    fl->v3fatal("Unknown setting for --x-assign: "<<argv[i]);
		}
	    }
	    else if ( !strcmp (sw, "-y") && (i+1)<argc ) {
		shift; addIncDirUser (parseFileArg(optdir,string (argv[i])));
	    }
	    else {
		fl->v3fatal ("Invalid Option: "<<argv[i]);
	    }
	    shift;
	} // - options
	else {
	    // Filename
	    string filename = parseFileArg(optdir,argv[i]);
	    if (suffixed(filename.c_str(), ".cpp")
		|| suffixed(filename.c_str(), ".cxx")
		|| suffixed(filename.c_str(), ".cc")
		|| suffixed(filename.c_str(), ".sp")) {
		V3Options::addCppFile(filename);
	    }
	    else if (suffixed(filename.c_str(), ".a")
		     || suffixed(filename.c_str(), ".o")
		     || suffixed(filename.c_str(), ".so")) {
		V3Options::addLdLibs(filename);
	    }
	    else {
		V3Options::addVFile(filename);
	    }
	    shift;
	}
    }
#undef shift
}

//======================================================================

void V3Options::parseOptsFile(FileLine* fl, const string& filename, bool rel) {
    // Read the specified -f filename and process as arguments
    UINFO(1,"Reading Options File "<<filename<<endl);

    const auto_ptr<ifstream> ifp (V3File::new_ifstream(filename));
    if (ifp->fail()) {
	fl->v3error("Cannot open -f command file: "+filename);
	return;
    }

    string whole_file;
    string::size_type pos;
    bool inCmt = false;
    while (!ifp->eof()) {
	string line;
	getline(*ifp, line);
	// Strip simple comments
	string oline;
	for (string::const_iterator pos = line.begin(); pos != line.end(); ++pos) {
	    if (inCmt) {
		if (*pos=='*' && *(pos+1)=='/') {
		    inCmt = false;
		    ++pos;
		}
	    } else if (*pos=='/' && *(pos+1)=='/') {
		break;  // Ignore to EOL
	    } else if (*pos=='/' && *(pos+1)=='*') {
		inCmt = true;
		// cppcheck-suppress StlMissingComparison
		++pos;
	    } else {
		oline += *pos;
	    }
	}
	whole_file += oline + " ";
    }
    whole_file += "\n";  // So string match below is simplified
    if (inCmt) fl->v3error("Unterminated /* comment inside -f file.");

    fl = new FileLine(filename, 0);

    // Split into argument list and process
    // Note we don't respect quotes.  It seems most simulators dont.
    // Woez those that expect it; we'll at least complain.
    if ((pos=whole_file.find("\"")) != string::npos) {
	fl->v3error("Double quotes in -f files cause unspecified behavior.");
    }

    // Strip off arguments and parse into words
    vector<string> args;
    string::size_type startpos = 0;
    while (startpos < whole_file.length()) {
	while (isspace(whole_file[startpos])) ++startpos;
	string::size_type endpos = startpos;
	while (endpos < whole_file.length() && !isspace(whole_file[endpos])) ++endpos;
	if (startpos != endpos) {
	    string arg (whole_file, startpos, endpos-startpos);
	    args.reserve(args.size()+1);
	    args.push_back(arg);
	}
	startpos = endpos;
    }

    // Path
    string optdir = (rel ? V3Options::filenameDir(filename) : ".");

    // Convert to argv style arg list and parse them
    char* argv [args.size()+1];
    for (unsigned i=0; i<args.size(); ++i) {
	argv[i] = (char*)args[i].c_str();
    }
    parseOptsList(fl, optdir, args.size(), argv);
}

//======================================================================

string V3Options::parseFileArg(const string& optdir, const string& relfilename) {
    string filename = V3Options::filenameSubstitute(relfilename);
    if (optdir != "." && filenameIsRel(filename)) {
	filename = optdir + "/" + filename;
    }
    return filename;
}

//======================================================================

void V3Options::showVersion(bool verbose) {
    cout <<version();
    cout <<endl;
    if (!verbose) return;

    cout <<endl;
    cout << "Copyright 2003-2012 by Wilson Snyder.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout <<endl;
    cout << "See http://www.veripool.org/verilator for documentation\n";

    cout <<endl;
    cout << "Summary of configuration:\n";
    cout << "  Compiled in defaults if not in environment:\n";
    cout << "    SYSTEMC            = " << DEFENV_SYSTEMC<<endl;
    cout << "    SYSTEMC_ARCH       = " << DEFENV_SYSTEMC_ARCH<<endl;
    cout << "    SYSTEMC_INCLUDE    = " << DEFENV_SYSTEMC_INCLUDE<<endl;
    cout << "    SYSTEMC_LIBDIR     = " << DEFENV_SYSTEMC_LIBDIR<<endl;
    cout << "    SYSTEMPERL         = " << DEFENV_SYSTEMPERL<<endl;
    cout << "    SYSTEMPERL_INCLUDE = " << DEFENV_SYSTEMPERL_INCLUDE<<endl;
    cout << "    VERILATOR_ROOT     = " << DEFENV_VERILATOR_ROOT<<endl;

    cout <<endl;
    cout << "Environment:\n";
    cout << "    PERL               = " << getenvStr("PERL","")<<endl;
    cout << "    SYSTEMC            = " << getenvStr("SYSTEMC","")<<endl;
    cout << "    SYSTEMC_ARCH       = " << getenvStr("SYSTEMC_ARCH","")<<endl;
    cout << "    SYSTEMC_INCLUDE    = " << getenvStr("SYSTEMC_INCLUDE","")<<endl;
    cout << "    SYSTEMC_LIBDIR     = " << getenvStr("SYSTEMC_LIBDIR","")<<endl;
    cout << "    SYSTEMPERL         = " << getenvStr("SYSTEMPERL","")<<endl;
    cout << "    SYSTEMPERL_INCLUDE = " << getenvStr("SYSTEMPERL_INCLUDE","")<<endl;
    cout << "    VERILATOR_ROOT     = " << getenvStr("VERILATOR_ROOT","")<<endl;
    cout << "    VERILATOR_BIN      = " << getenvStr("VERILATOR_BIN","")<<endl;  // wrapper uses this
}

//======================================================================

V3Options::V3Options() {
    m_impp = new V3OptionsImp;

    m_autoflush = false;
    m_coverageLine = false;
    m_coverageToggle = false;
    m_coverageUnderscore = false;
    m_coverageUser = false;
    m_debugCheck = false;
    m_dumpTree = false;
    m_exe = false;
    m_ignc = false;
    m_l2Name = true;
    m_lintOnly = false;
    m_makeDepend = true;
    m_makePhony = false;
    m_outFormatOk = false;
    m_warnFatal = true;
    m_pinsBv = 65;
    m_profileCFuncs = false;
    m_preprocOnly = false;
    m_psl = false;
    m_public = false;
    m_skipIdentical = true;
    m_stats = false;
    m_systemC = false;
    m_systemPerl = false;
    m_trace = false;
    m_traceDups = false;
    m_traceUnderscore = false;
    m_underlineZero = false;

    m_errorLimit = 50;
    m_ifDepth = 0;
    m_inlineMult = 2000;
    m_outputSplit = 0;
    m_outputSplitCFuncs = 0;
    m_outputSplitCTrace = 0;
    m_traceDepth = 0;
    m_traceMaxArray = 32;
    m_traceMaxWidth = 256;
    m_unrollCount = 64;
    m_unrollStmts = 30000;

    m_compLimitParens = 0;
    m_compLimitBlocks = 0;

    m_makeDir = "obj_dir";
    m_bin = "";
    m_flags = "";
    m_unusedRegexp = "*unused*";
    m_xAssign = "fast";

    m_language = V3LangCode::mostRecent();

    optimize(true);
    // Default +libext+
    addLibExtV("");  // So include "filename.v" will find the same file
    addLibExtV(".v");
    addLibExtV(".sv");
    // Default -I
    addIncDirFallback(".");	// Looks better than {long_cwd_path}/...
}

V3Options::~V3Options() {
    delete m_impp; m_impp=NULL;
}

void V3Options::setDebugMode(int level) {
    V3Error::debugDefault(level);
    m_dumpTree = true;
    m_stats = true;
    m_debugCheck = true;
    cout << "Starting "<<version()<<endl;
}

void V3Options::setDebugSrcLevel(const string& srcfile, int level) {
    DebugSrcMap::iterator iter = m_debugSrcs.find(srcfile);
    if (iter!=m_debugSrcs.end()) {
	iter->second = level;
    } else {
	m_debugSrcs.insert(make_pair(srcfile,level));
    }
}

int V3Options::debugSrcLevel(const string& srcfile_path, int default_level) {
    // For simplicity, calling functions can just use __FILE__ for srcfile.
    // That means though we need to cleanup the filename from ../Foo.cpp -> Foo
    string srcfile = V3Options::filenameNonDirExt(srcfile_path);
    DebugSrcMap::iterator iter = m_debugSrcs.find(srcfile);
    if (iter!=m_debugSrcs.end()) {
	return iter->second;
    } else {
	return default_level;
    }
}

void V3Options::optimize(int level) {
    // Set all optimizations to on/off
    bool flag = level > 0;
    m_oAcycSimp = flag;
    m_oCase = flag;
    m_oCombine = flag;
    m_oConst = flag;
    m_oExpand = flag;
    m_oFlopGater = flag;
    m_oGate = flag;
    m_oInline = flag;
    m_oLife = flag;
    m_oLifePost = flag;
    m_oLocalize = flag;
    m_oReorder = flag;
    m_oSplit = flag;
    m_oSubst = flag;
    m_oSubstConst = flag;
    m_oTable = flag;
    // And set specific optimization levels
    if (level >= 3) {
	m_inlineMult = -1;	// Maximum inlining
    }
}
