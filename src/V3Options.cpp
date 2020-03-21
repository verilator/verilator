// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3Os.h"
#include "V3Options.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3PreShell.h"

#include <sys/types.h>
#include <sys/stat.h>
#ifndef _WIN32
# include <sys/utsname.h>
#endif
#include <cctype>
#include <dirent.h>
#include <fcntl.h>
#include <list>
#include <map>
#include <memory>
#include <set>

#include "config_rev.h"

#if defined(_WIN32) || defined(__MINGW32__)
# include <io.h>  // open, close
#endif

//######################################################################
// V3 Internal state

class V3OptionsImp {
public:
    // TYPES
    typedef std::map<string,std::set<string> > DirMap;  // Directory listing

    // STATE
    std::list<string>   m_allArgs;      // List of every argument encountered
    std::list<string>   m_incDirUsers;          // Include directories (ordered)
    std::set<string>    m_incDirUserSet;        // Include directories (for removing duplicates)
    std::list<string>   m_incDirFallbacks;      // Include directories (ordered)
    std::set<string>    m_incDirFallbackSet;    // Include directories (for removing duplicates)
    std::map<string,V3LangCode> m_langExts;             // Language extension map
    std::list<string>   m_libExtVs;     // Library extensions (ordered)
    std::set<string>    m_libExtVSet;   // Library extensions (for removing duplicates)
    DirMap              m_dirMap;       // Directory listing

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
    void addLangExt(const string& langext, const V3LangCode& lc) {
        // New language extension replaces any pre-existing one.
        (void)m_langExts.erase(langext);
        m_langExts[langext] = lc;
    }

    void addLibExtV(const string& libext) {
        if (m_libExtVSet.find(libext) == m_libExtVSet.end()) {
            m_libExtVSet.insert(libext);
            m_libExtVs.push_back(libext);
        }
    }
    V3OptionsImp() {}
    ~V3OptionsImp() {}
};

//######################################################################
// V3LangCode class functions

V3LangCode::V3LangCode(const char* textp) {
    // Return code for given string, or ERROR, which is a bad code
    for (int codei = V3LangCode::L_ERROR; codei < V3LangCode::_ENUM_END; ++codei) {
        V3LangCode code = V3LangCode(codei);
        if (0 == VL_STRCASECMP(textp, code.ascii())) {
            m_e = code;
            return;
        }
    }
    m_e = V3LangCode::L_ERROR;
}

//######################################################################
// V3Options class functions

void V3Options::addIncDirUser(const string& incdir) {
    m_impp->addIncDirUser(incdir);
}
void V3Options::addIncDirFallback(const string& incdir) {
    m_impp->addIncDirFallback(incdir);
}
void V3Options::addLangExt(const string& langext, const V3LangCode& lc) {
    m_impp->addLangExt(langext, lc);
}
void V3Options::addLibExtV(const string& libext) {
    m_impp->addLibExtV(libext);
}
void V3Options::addDefine(const string& defline, bool allowPlus) {
    // Split +define+foo=value into the appropriate parts and parse
    // Optional + says to allow multiple defines on the line
    // + is not quotable, as other simulators do not allow that
    string left = defline;
    while (left != "") {
        string def = left;
        string::size_type pos;
        if (allowPlus && ((pos = left.find('+')) != string::npos)) {
            left = left.substr(pos+1);
            def.erase(pos);
        } else {
            left = "";
        }
        string value;
        if ((pos = def.find('=')) != string::npos) {
            value = def.substr(pos+1);
            def.erase(pos);
        }
        V3PreShell::defineCmdLine(def, value);
    }
}
void V3Options::addParameter(const string& paramline, bool allowPlus) {
    // Split +define+foo=value into the appropriate parts and parse
    // Optional + says to allow multiple defines on the line
    // + is not quotable, as other simulators do not allow that
    string left = paramline;
    while (left != "") {
        string param = left;
        string::size_type pos;
        if (allowPlus && ((pos = left.find('+')) != string::npos)) {
            left = left.substr(pos+1);
            param.erase(pos);
        } else {
            left = "";
        }
        string value;
        if ((pos = param.find('=')) != string::npos) {
            value = param.substr(pos+1);
            param.erase(pos);
        }
        UINFO(4,"Add parameter"<<param<<"="<<value<<endl);
        (void)m_parameters.erase(param);
        m_parameters[param] = value;
    }
}

bool V3Options::hasParameter(const string& name) {
    return m_parameters.find(name) != m_parameters.end();
}

string V3Options::parameter(const string& name) {
    string value = m_parameters.find(name)->second;
    m_parameters.erase(m_parameters.find(name));
    return value;
}

void V3Options::checkParameters() {
    if (!m_parameters.empty()) {
        std::stringstream msg;
        msg << "Parameters from the command line were not found in the design:";
        for (std::map<string,string>::iterator it = m_parameters.begin();
                it != m_parameters.end(); ++it) {
            msg << " " << it->first;
        }
        v3error(msg.str());
    }
}

void V3Options::addCppFile(const string& filename) {
    m_cppFiles.insert(filename);
}
void V3Options::addCFlags(const string& filename) {
    m_cFlags.push_back(filename);
}
void V3Options::addLdLibs(const string& filename) {
    m_ldLibs.push_back(filename);
}
void V3Options::addFuture(const string& flag) {
    m_futures.insert(flag);
}
bool V3Options::isFuture(const string& flag) const {
    return m_futures.find(flag) != m_futures.end();
}
bool V3Options::isLibraryFile(const string& filename) const {
    return m_libraryFiles.find(filename) != m_libraryFiles.end();
}
void V3Options::addLibraryFile(const string& filename) {
    m_libraryFiles.insert(filename);
}
bool V3Options::isClocker(const string& signame) const {
    return m_clockers.find(signame) != m_clockers.end();
}
void V3Options::addClocker(const string& signame) {
    m_clockers.insert(signame);
}
bool V3Options::isNoClocker(const string& signame) const {
    return m_noClockers.find(signame) != m_noClockers.end();
}
void V3Options::addNoClocker(const string& signame) {
    m_noClockers.insert(signame);
}
void V3Options::addVFile(const string& filename) {
    // We use a list for v files, because it's legal to have includes
    // in a specific order and multiple of them.
    m_vFiles.push_back(filename);
}
void V3Options::addForceInc(const string& filename) {
    m_forceIncs.push_back(filename);
}

void V3Options::addArg(const string& arg) {
    m_impp->m_allArgs.push_back(arg);
}

string V3Options::allArgsString() {
    string out;
    for (std::list<string>::const_iterator it = m_impp->m_allArgs.begin();
         it != m_impp->m_allArgs.end(); ++it) {
        if (out != "") out += " ";
        out += *it;
    }
    return out;
}

//######################################################################
// File searching

bool V3Options::fileStatDir(const string& filename) {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    struct stat sstat;  // Stat information
    int err = stat(filename.c_str(), &sstat);
    if (err!=0) return false;
    if (!S_ISDIR(sstat.st_mode)) return false;
    return true;
}

bool V3Options::fileStatNormal(const string& filename) {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    struct stat sstat;  // Stat information
    int err = stat(filename.c_str(), &sstat);
    if (err!=0) return false;
    if (S_ISDIR(sstat.st_mode)) return false;
    return true;
}

void V3Options::fileNfsFlush(const string& filename) {
    // NFS caches stat() calls so to get up-to-date information must
    // do a open or opendir on the filename.
    // Faster to just try both rather than check if a file is a dir.
    if (DIR* dirp = opendir(filename.c_str())) {
        closedir(dirp);
    } else if (int fd = ::open(filename.c_str(), O_RDONLY)) {
        if (fd>0) ::close(fd);
    }
}

string V3Options::fileExists(const string& filename) {
    // Surprisingly, for VCS and other simulators, this process
    // is quite slow; presumably because of re-reading each directory
    // many times.  So we read a whole dir at once and cache it

    string dir = V3Os::filenameDir(filename);
    string basename = V3Os::filenameNonDir(filename);

    V3OptionsImp::DirMap::iterator diriter = m_impp->m_dirMap.find(dir);
    if (diriter == m_impp->m_dirMap.end()) {
        // Read the listing
        m_impp->m_dirMap.insert(std::make_pair(dir, std::set<string>() ));
        diriter = m_impp->m_dirMap.find(dir);

        std::set<string>* setp = &(diriter->second);

        if (DIR* dirp = opendir(dir.c_str())) {
            while (struct dirent* direntp = readdir(dirp)) {

                setp->insert(direntp->d_name);
            }
            closedir(dirp);
        }
    }
    // Find it
    std::set<string>* filesetp = &(diriter->second);
    std::set<string>::iterator fileiter = filesetp->find(basename);
    if (fileiter == filesetp->end()) {
        return "";  // Not found
    }
    // Check if it is a directory, ignore if so
    string filenameOut = V3Os::filenameFromDirBase(dir, basename);
    if (!fileStatNormal(filenameOut)) return "";  // Directory
    return filenameOut;
}

string V3Options::filePathCheckOneDir(const string& modname, const string& dirname) {
    for (std::list<string>::iterator extIter=m_impp->m_libExtVs.begin();
         extIter != m_impp->m_libExtVs.end(); ++extIter) {
        string fn = V3Os::filenameFromDirBase(dirname, modname+*extIter);
        string exists = fileExists(fn);
        if (exists!="") {
            // Strip ./, it just looks ugly
            if (exists.substr(0, 2)=="./") exists.erase(0, 2);
            return exists;
        }
    }
    return "";
}

string V3Options::filePath(FileLine* fl, const string& modname, const string& lastpath,
                           const string& errmsg) {  // Error prefix or "" to suppress error
    // Find a filename to read the specified module name,
    // using the incdir and libext's.
    // Return "" if not found.
    for (std::list<string>::iterator dirIter=m_impp->m_incDirUsers.begin();
         dirIter!=m_impp->m_incDirUsers.end(); ++dirIter) {
        string exists = filePathCheckOneDir(modname, *dirIter);
        if (exists!="") return exists;
    }
    for (std::list<string>::iterator dirIter=m_impp->m_incDirFallbacks.begin();
         dirIter!=m_impp->m_incDirFallbacks.end(); ++dirIter) {
        string exists = filePathCheckOneDir(modname, *dirIter);
        if (exists!="") return exists;
    }

    if (m_relativeIncludes) {
        string exists = filePathCheckOneDir(modname, lastpath);
        if (exists!="") return V3Os::filenameRealPath(exists);
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
    if (modname.find("__Vhsh") != string::npos) {
        std::cerr << V3Error::warnMore() << "... Unsupported: Name is longer than 127 characters;"
                  << " automatic file lookup not supported.\n";
        std::cerr << V3Error::warnMore() << "... Suggest putting filename with this module/package"
                  << " onto command line instead.\n";
    } else if (!shown_notfound_msg) {
        shown_notfound_msg = true;
        if (m_impp->m_incDirUsers.empty()) {
            fl->v3error("This may be because there's no search path specified with -I<dir>."<<endl);
        }
        std::cerr<<V3Error::warnMore()<<"... Looked in:"<<endl;
        for (std::list<string>::iterator dirIter=m_impp->m_incDirUsers.begin();
             dirIter!=m_impp->m_incDirUsers.end(); ++dirIter) {
            for (std::list<string>::iterator extIter=m_impp->m_libExtVs.begin();
                 extIter != m_impp->m_libExtVs.end(); ++extIter) {
                string fn = V3Os::filenameFromDirBase(*dirIter, modname+*extIter);
                std::cerr<<V3Error::warnMore()<<"     "<<fn<<endl;
            }
        }
        for (std::list<string>::iterator dirIter=m_impp->m_incDirFallbacks.begin();
             dirIter!=m_impp->m_incDirFallbacks.end(); ++dirIter) {
            for (std::list<string>::iterator extIter=m_impp->m_libExtVs.begin();
                 extIter != m_impp->m_libExtVs.end(); ++extIter) {
                string fn = V3Os::filenameFromDirBase(*dirIter, modname+*extIter);
                std::cerr<<V3Error::warnMore()<<"     "<<fn<<endl;
            }
        }
    }
}

//! Determine what language is associated with a filename

//! If we recognize the extension, use its language, otherwise, use the
//! default language.
V3LangCode V3Options::fileLanguage(const string &filename) {
    string ext = V3Os::filenameNonDir(filename);
    string::size_type pos;
    if ((pos = ext.rfind('.')) != string::npos) {
        ext.erase(0, pos + 1);
        std::map<string,V3LangCode>::iterator it = m_impp->m_langExts.find(ext);
        if (it != m_impp->m_langExts.end()) {
            return it->second;
        }
    }
    return m_defaultLanguage;
}


//######################################################################
// Environment

string V3Options::getenvBuiltins(const string& var) {
    if (var == "PERL") return getenvPERL();
    else if (var == "SYSTEMC") return getenvSYSTEMC();
    else if (var == "SYSTEMC_ARCH") return getenvSYSTEMC_ARCH();
    else if (var == "SYSTEMC_INCLUDE") return getenvSYSTEMC_INCLUDE();
    else if (var == "SYSTEMC_LIBDIR") return getenvSYSTEMC_LIBDIR();
    else if (var == "VERILATOR_ROOT") return getenvVERILATOR_ROOT();
    else {
        return V3Os::getenvStr(var, "");
    }
}

string V3Options::getenvPERL() {
    return V3Os::getenvStr("PERL", "perl");
}

string V3Options::getenvSYSTEMC() {
    string var = V3Os::getenvStr("SYSTEMC", "");
    if (var == "" && string(DEFENV_SYSTEMC) != "") {
        var = DEFENV_SYSTEMC;
        V3Os::setenvStr("SYSTEMC", var, "Hardcoded at build time");
    }
    return var;
}

string V3Options::getenvSYSTEMC_ARCH() {
    string var = V3Os::getenvStr("SYSTEMC_ARCH", "");
    if (var == "" && string(DEFENV_SYSTEMC_ARCH) != "") {
        var = DEFENV_SYSTEMC_ARCH;
        V3Os::setenvStr("SYSTEMC_ARCH", var, "Hardcoded at build time");
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
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
        struct utsname uts;
        uname(&uts);
        string sysname = VString::downcase(uts.sysname);  // aka  'uname -s'
        if (VString::wildmatch(sysname.c_str(), "*solaris*")) { var = "gccsparcOS5"; }
        else if (VString::wildmatch(sysname.c_str(), "*cygwin*")) { var = "cygwin"; }
        else { var = "linux"; }
#endif
        V3Os::setenvStr("SYSTEMC_ARCH", var, "From sysname '"+sysname+"'");
    }
    return var;
}

string V3Options::getenvSYSTEMC_INCLUDE() {
    string var = V3Os::getenvStr("SYSTEMC_INCLUDE", "");
    if (var == "" && string(DEFENV_SYSTEMC_INCLUDE) != "") {
        var = DEFENV_SYSTEMC_INCLUDE;
        V3Os::setenvStr("SYSTEMC_INCLUDE", var, "Hardcoded at build time");
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
    string var = V3Os::getenvStr("SYSTEMC_LIBDIR", "");
    if (var == "" && string(DEFENV_SYSTEMC_LIBDIR) != "") {
        var = DEFENV_SYSTEMC_LIBDIR;
        V3Os::setenvStr("SYSTEMC_LIBDIR", var, "Hardcoded at build time");
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

string V3Options::getenvVERILATOR_ROOT() {
    string var = V3Os::getenvStr("VERILATOR_ROOT", "");
    if (var == "" && string(DEFENV_VERILATOR_ROOT) != "") {
        var = DEFENV_VERILATOR_ROOT;
        V3Os::setenvStr("VERILATOR_ROOT", var, "Hardcoded at build time");
    }
    if (var == "") {
        v3fatal("$VERILATOR_ROOT needs to be in environment\n");
    }
    return var;
}

//######################################################################
// V3 Options notification methods

void V3Options::notify() {
    // Notify that all arguments have been passed and final modification can be made.
    if (!outFormatOk()
        && !cdc()
        && !dpiHdrOnly()
        && !lintOnly()
        && !preprocOnly()
        && !xmlOnly()) {
        v3fatal("verilator: Need --cc, --sc, --cdc, --dpi-hdr-only, --lint-only, --xml-only or --E option");
    }

    // Make sure at least one make system is enabled
    if (!m_gmake && !m_cmake) {
        m_gmake = true;
    }

    if (protectIds()) {
        FileLine* cmdfl = new FileLine(FileLine::commandLineFilename());
        if (allPublic()) {
            // We always call protect() on names, we don't check if public or not
            // Hence any external references wouldn't be able to find the refed public object.
            cmdfl->v3error("Unsupported: Using --protect-ids with --public\n"
                           +V3Error::warnMore()+"... Suggest remove --public.");
        }
        if (trace()) {
            cmdfl->v3warn(INSECURE,
                          "Using --protect-ids with --trace may expose private design details\n"
                          +V3Error::warnMore()+"... Suggest remove --trace.");
        }
        if (vpi()) {
            cmdfl->v3warn(INSECURE,
                          "Using --protect-ids with --vpi may expose private design details\n"
                          +V3Error::warnMore()+"... Suggest remove --vpi.");
        }
    }

    // Default some options if not turned on or off
    if (v3Global.opt.skipIdentical().isDefault()) {
        v3Global.opt.m_skipIdentical.setTrueOrFalse(
            !v3Global.opt.cdc()
            && !v3Global.opt.dpiHdrOnly()
            && !v3Global.opt.lintOnly()
            && !v3Global.opt.preprocOnly()
            && !v3Global.opt.xmlOnly());
    }
    if (v3Global.opt.makeDepend().isDefault()) {
        v3Global.opt.m_makeDepend.setTrueOrFalse(
            !v3Global.opt.cdc()
            && !v3Global.opt.dpiHdrOnly()
            && !v3Global.opt.lintOnly()
            && !v3Global.opt.preprocOnly()
            && !v3Global.opt.xmlOnly());
    }
}

//######################################################################
// V3 Options accessors

string V3Options::version() {
    string ver = DTVERSION;
    ver += " rev "+cvtToStr(DTVERSION_rev);
    return ver;
}

string V3Options::protectKeyDefaulted() {
    if (m_protectKey.empty()) {
        // Create a key with a human-readable symbol-like name.
        // This conversion drops ~2 bits of entropy out of 256, shouldn't matter.
        VHashSha256 digest (V3Os::trueRandom(32));
        m_protectKey = "VL-KEY-"+digest.digestSymbol();
    }
    return m_protectKey;
}

void V3Options::throwSigsegv() {
#if !(defined(VL_CPPCHECK) || defined(__clang_analyzer__))
    char* zp=NULL; *zp=0;  // Intentional core dump, ignore warnings here
#endif
}

//######################################################################
// V3 Options utilities

string V3Options::argString(int argc, char** argv) {
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

void V3Options::parseOpts(FileLine* fl, int argc, char** argv) {
    // Parse all options
    // Initial entry point from Verilator.cpp
    parseOptsList(fl, ".", argc, argv);

    // Default certain options and error check
    // Detailed error, since this is what we often get when run with minimal arguments
    const V3StringList& vFilesList = vFiles();
    if (vFilesList.empty()) {
        v3fatal("verilator: No Input Verilog file specified on command line, see verilator --help for more information\n");
    }

    // Default prefix to the filename
    if (prefix()=="" && topModule()!="") m_prefix = string("V")+topModule();
    if (prefix()=="" && vFilesList.size()>=1) {
        m_prefix = string("V")+V3Os::filenameNonExt(*(vFilesList.begin()));
    }
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
    if (arg[0]!='-') v3fatalSrc("OnOff switches must have leading dash");
    if (0==strcmp(sw, arg)) { flag = true; return true; }
    else if (0==strncmp(sw, "-no", 3) && (0==strcmp(sw+3, arg+1))) { flag = false; return true; }
    else if (0==strncmp(sw, "-no-", 4) && (0==strcmp(sw+4, arg+1))) { flag = false; return true; }
    return false;
}
bool V3Options::onoffb(const char* sw, const char* arg, VOptionBool& bflag) {
    bool flag;
    if (onoff(sw, arg, flag/*ref*/)) {
        bflag.setTrueOrFalse(flag);
        return true;
    } else {
        return false;
    }
}

bool V3Options::suffixed(const string& sw, const char* arg) {
    if (strlen(arg) > sw.length()) return false;
    return (0==strcmp(sw.c_str()+sw.length()-strlen(arg), arg));
}

void V3Options::parseOptsList(FileLine* fl, const string& optdir, int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
    for (int i=0; i<argc; ++i)  {
        addArg(argv[i]);  // -f's really should be inserted in the middle, but this is for debug
    }
#define shift { ++i; }
    for (int i=0; i<argc; )  {
        UINFO(9, " Option: "<<argv[i]<<endl);
        if (argv[i][0]=='+') {
            char* sw = argv[i];
            if (!strncmp (sw, "+define+", 8)) {
                addDefine(string(sw+strlen("+define+")), true);
            }
            else if (!strncmp (sw, "+incdir+", 8)) {
                addIncDirUser(parseFileArg(optdir, string(sw+strlen("+incdir+"))));
            }
            else if (parseLangExt(sw, "+systemverilogext+", V3LangCode::L1800_2017)
                     || parseLangExt(sw, "+verilog1995ext+", V3LangCode::L1364_1995)
                     || parseLangExt(sw, "+verilog2001ext+", V3LangCode::L1364_2001)
                     || parseLangExt(sw, "+1364-1995ext+", V3LangCode::L1364_1995)
                     || parseLangExt(sw, "+1364-2001ext+", V3LangCode::L1364_2001)
                     || parseLangExt(sw, "+1364-2005ext+", V3LangCode::L1364_2005)
                     || parseLangExt(sw, "+1800-2005ext+", V3LangCode::L1800_2005)
                     || parseLangExt(sw, "+1800-2009ext+", V3LangCode::L1800_2009)
                     || parseLangExt(sw, "+1800-2012ext+", V3LangCode::L1800_2012)
                     || parseLangExt(sw, "+1800-2017ext+", V3LangCode::L1800_2017)) {
                // Nothing to do here - all done in the test

            }
            else if (!strncmp (sw, "+libext+", 8)) {
                string exts = string(sw+strlen("+libext+"));
                string::size_type pos;
                while ((pos = exts.find('+')) != string::npos) {
                    addLibExtV(exts.substr(0, pos));
                    exts = exts.substr(pos+1);
                }
                addLibExtV(exts);
            }
            else if (!strcmp(sw, "+librescan")) {  // NOP
            }
            else if (!strcmp(sw, "+notimingchecks")) {  // NOP
            }
            else {
                fl->v3fatal("Invalid Option: "<<argv[i]);
            }
            shift;
        }  // + options
        else if (argv[i][0]=='-') {
            const char* sw = argv[i];
            bool flag = true;
            VOptionBool bflag;
            // Allow gnu -- switches
            if (sw[0]=='-' && sw[1]=='-') ++sw;
            bool hadSwitchPart1 = true;
            if (0) {}
            // Single switches
            else if (!strcmp(sw, "-E"))                         { m_preprocOnly = true; }
            else if ( onoffb(sw, "-MMD", bflag/*ref*/))         { m_makeDepend = bflag; }
            else if ( onoff (sw, "-MP", flag/*ref*/))           { m_makePhony = flag; }
            else if (!strcmp(sw, "-P"))                         { m_preprocNoLine = true; }
            else if ( onoff (sw, "-assert", flag/*ref*/))       { m_assert = flag; }
            else if ( onoff (sw, "-autoflush", flag/*ref*/))    { m_autoflush = flag; }
            else if ( onoff (sw, "-bbox-sys", flag/*ref*/))     { m_bboxSys = flag; }
            else if ( onoff (sw, "-bbox-unsup", flag/*ref*/))   { m_bboxUnsup = flag; }
            else if (!strcmp(sw, "-cc"))                        { m_outFormatOk = true; m_systemC = false; }
            else if ( onoff (sw, "-cdc", flag/*ref*/))          { m_cdc = flag; }
            else if ( onoff (sw, "-coverage", flag/*ref*/))     { coverage(flag); }
            else if ( onoff (sw, "-coverage-line", flag/*ref*/)){ m_coverageLine = flag; }
            else if ( onoff (sw, "-coverage-toggle", flag/*ref*/)){ m_coverageToggle = flag; }
            else if ( onoff (sw, "-coverage-underscore", flag/*ref*/)){ m_coverageUnderscore = flag; }
            else if ( onoff (sw, "-coverage-user", flag/*ref*/)){ m_coverageUser = flag; }
            else if ( onoff (sw, "-covsp", flag/*ref*/))        { }  // TBD
            else if (!strcmp(sw, "-debug-abort")) { abort(); }  // Undocumented, see also --debug-sigsegv
            else if ( onoff (sw, "-debug-check", flag/*ref*/))  { m_debugCheck = flag; }
            else if ( onoff (sw, "-debug-collision", flag/*ref*/)) { m_debugCollision = flag; }  // Undocumented
            else if ( onoff (sw, "-debug-leak", flag/*ref*/))   { m_debugLeak = flag; }
            else if ( onoff (sw, "-debug-nondeterminism", flag/*ref*/)){ m_debugNondeterminism = flag; }
            else if ( onoff (sw, "-debug-partition", flag/*ref*/)){ m_debugPartition = flag; }  // Undocumented
            else if ( onoff (sw, "-debug-protect", flag/*ref*/)){ m_debugProtect = flag; }  // Undocumented
            else if ( onoff (sw, "-debug-self-test", flag/*ref*/)){ m_debugSelfTest = flag; }  // Undocumented
            else if (!strcmp(sw, "-debug-sigsegv"))             { throwSigsegv(); }  // Undocumented, see also --debug-abort
            else if (!strcmp(sw, "-debug-fatalsrc"))            { v3fatalSrc("--debug-fatal-src"); }  // Undocumented, see also --debug-abort
            else if ( onoff (sw, "-decoration", flag/*ref*/))   { m_decoration = flag; }
            else if ( onoff (sw, "-dpi-hdr-only", flag/*ref*/)) { m_dpiHdrOnly = flag; }
            else if ( onoff (sw, "-dump-defines", flag/*ref*/)) { m_dumpDefines = flag; }
            else if ( onoff (sw, "-dump-tree", flag/*ref*/))    { m_dumpTree = flag ? 3 : 0; }  // Also see --dump-treei
            else if ( onoff (sw, "-exe", flag/*ref*/))          { m_exe = flag; }
            else if ( onoff (sw, "-ignc", flag/*ref*/))         { m_ignc = flag; }
            else if ( onoff (sw, "-inhibit-sim", flag/*ref*/))  { m_inhibitSim = flag; }
            else if ( onoff (sw, "-lint-only", flag/*ref*/))    { m_lintOnly = flag; }
            else if (!strcmp(sw, "-no-pins64"))                 { m_pinsBv = 33; }
            else if ( onoff (sw, "-order-clock-delay", flag/*ref*/)) { m_orderClockDly = flag; }
            else if (!strcmp(sw, "-pins64"))                    { m_pinsBv = 65; }
            else if ( onoff (sw, "-pins-sc-uint", flag/*ref*/)) { m_pinsScUint = flag; if (!m_pinsScBigUint) m_pinsBv = 65; }
            else if ( onoff (sw, "-pins-sc-biguint", flag/*ref*/)){ m_pinsScBigUint = flag; m_pinsBv = 513; }
            else if ( onoff (sw, "-pins-uint8", flag/*ref*/))   { m_pinsUint8 = flag; }
            else if ( onoff (sw, "-pp-comments", flag/*ref*/))  { m_ppComments = flag; }
            else if (!strcmp(sw, "-private"))                   { m_public = false; }
            else if ( onoff (sw, "-prof-cfuncs", flag/*ref*/))       { m_profCFuncs = flag; }
            else if ( onoff (sw, "-profile-cfuncs", flag/*ref*/))    { m_profCFuncs = flag; }  // Undocumented, for backward compat
            else if ( onoff (sw, "-prof-threads", flag/*ref*/))      { m_profThreads = flag; }
            else if ( onoff (sw, "-protect-ids", flag/*ref*/))       { m_protectIds = flag; }
            else if ( onoff (sw, "-public", flag/*ref*/))            { m_public = flag; }
            else if ( onoff (sw, "-public-flat-rw", flag/*ref*/) )   { m_publicFlatRW = flag; v3Global.dpi(true); }
            else if (!strncmp(sw, "-pvalue+", strlen("-pvalue+")))   { addParameter(string(sw+strlen("-pvalue+")), false); }
            else if ( onoff (sw, "-quiet-exit", flag/*ref*/))        { m_quietExit = flag; }
            else if ( onoff (sw, "-relative-cfuncs", flag/*ref*/))   { m_relativeCFuncs = flag; }
            else if ( onoff (sw, "-relative-includes", flag/*ref*/)) { m_relativeIncludes = flag; }
            else if ( onoff (sw, "-report-unoptflat", flag/*ref*/))  { m_reportUnoptflat = flag; }
            else if ( onoff (sw, "-savable", flag/*ref*/))           { m_savable = flag; }
            else if (!strcmp(sw, "-sc"))                             { m_outFormatOk = true; m_systemC = true; }
            else if ( onoffb(sw, "-skip-identical", bflag/*ref*/))   { m_skipIdentical = bflag; }
            else if ( onoff (sw, "-stats", flag/*ref*/))             { m_stats = flag; }
            else if ( onoff (sw, "-stats-vars", flag/*ref*/))        { m_statsVars = flag; m_stats |= flag; }
            else if ( onoff (sw, "-structs-unpacked", flag/*ref*/))  { m_structsPacked = flag; }
            else if (!strcmp(sw, "-sv"))                             { m_defaultLanguage = V3LangCode::L1800_2005; }
            else if ( onoff (sw, "-threads-coarsen", flag/*ref*/))   { m_threadsCoarsen = flag; }  // Undocumented, debug
            else if ( onoff (sw, "-trace", flag/*ref*/))             { m_trace = flag; }
            else if ( onoff (sw, "-trace-coverage", flag/*ref*/))    { m_traceCoverage = flag; }
            else if ( onoff (sw, "-trace-dups", flag/*ref*/))        { m_traceDups = flag; }
            else if ( onoff (sw, "-trace-params", flag/*ref*/))      { m_traceParams = flag; }
            else if ( onoff (sw, "-trace-structs", flag/*ref*/))     { m_traceStructs = flag; }
            else if ( onoff (sw, "-trace-underscore", flag/*ref*/))  { m_traceUnderscore = flag; }
            else if ( onoff (sw, "-underline-zero", flag/*ref*/))    { m_underlineZero = flag; }  // Undocumented, old Verilator-2
            else if ( onoff (sw, "-vpi", flag/*ref*/))               { m_vpi = flag; }
            else if ( onoff (sw, "-Wpedantic", flag/*ref*/))         { m_pedantic = flag; }
            else if ( onoff (sw, "-x-initial-edge", flag/*ref*/))    { m_xInitialEdge = flag; }
            else if ( onoff (sw, "-xml-only", flag/*ref*/))          { m_xmlOnly = flag; }  // Undocumented, still experimental
            else { hadSwitchPart1 = false; }
            if (hadSwitchPart1) {}
            // Optimization
            else if (!strncmp (sw, "-O", 2)) {
                for (const char* cp=sw+strlen("-O"); *cp; ++cp) {
                    flag = isupper(*cp);
                    switch (tolower(*cp)) {
                    case '0': optimize(0); break;  // 0=all off
                    case '1': optimize(1); break;  // 1=all on
                    case '2': optimize(2); break;  // 2=not used
                    case '3': optimize(3); break;  // 3=high
                    case 'a': m_oTable = flag; break;
                    case 'b': m_oCombine = flag; break;
                    case 'c': m_oConst = flag; break;
                    case 'd': m_oDedupe = flag; break;
                    case 'm': m_oAssemble = flag; break;
                    case 'e': m_oCase = flag; break;
                    case 'g': m_oGate = flag; break;
                    case 'i': m_oInline = flag; break;
                    case 'k': m_oSubstConst = flag; break;
                    case 'l': m_oLife = flag; break;
                    case 'p': m_public = !flag; break;  // With -Op so flag=0, we want public on so few optimizations done
                    case 'r': m_oReorder = flag; break;
                    case 's': m_oSplit = flag; break;
                    case 't': m_oLifePost = flag; break;
                    case 'u': m_oSubst = flag; break;
                    case 'v': m_oReloop = flag; break;
                    case 'x': m_oExpand = flag; break;
                    case 'y': m_oAcycSimp = flag; break;
                    case 'z': m_oLocalize = flag; break;
                    default:  break;  // No error, just ignore
                    }
                }
            }
            // Parameterized switches
            else if (!strcmp(sw, "-CFLAGS") && (i+1)<argc) {
                shift;
                addCFlags(argv[i]);
            }
            else if (!strcmp(sw, "-comp-limit-blocks") && (i+1)<argc) {  // Undocumented
                shift;
                m_compLimitBlocks = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-comp-limit-members") && (i+1)<argc) {  // Undocumented
                shift;
                m_compLimitMembers = atoi(argv[i]);  // Ideally power-of-two so structs stay aligned
            }
            else if (!strcmp(sw, "-comp-limit-parens") && (i+1)<argc) {  // Undocumented
                shift;
                m_compLimitParens = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-comp-limit-syms") && (i+1)<argc) {  // Undocumented
                shift;
                VName::maxLength(atoi(argv[i]));
            }
            else if (!strcmp(sw, "-converge-limit") && (i+1)<argc) {
                shift;
                m_convergeLimit = atoi(argv[i]);
            }
            else if (!strncmp (sw, "-D", 2)) {
                addDefine(string(sw+strlen("-D")), false);
            }
            else if (!strcmp(sw, "-debug")) {
                setDebugMode(3);
            }
            else if (!strcmp(sw, "-debugi") && (i+1)<argc) {
                shift;
                setDebugMode(atoi(argv[i]));
            }
            else if (!strncmp (sw, "-debugi-", strlen("-debugi-"))) {
                const char* src = sw+strlen("-debugi-");
                shift;
                setDebugSrcLevel(src, atoi(argv[i]));
            }
            else if (!strcmp(sw, "-dump-treei") && (i+1)<argc) {
                shift;
                m_dumpTree = atoi(argv[i]);
            }
            else if (!strncmp (sw, "-dump-treei-", strlen("-dump-treei-"))) {
                const char* src = sw+strlen("-dump-treei-");
                shift;
                setDumpTreeLevel(src, atoi(argv[i]));
            }
            else if (!strcmp(sw, "-error-limit") && (i+1)<argc) {
                shift;
                V3Error::errorLimit(atoi(argv[i]));
            }
            else if (!strcmp(sw, "-FI") && (i+1)<argc) {
                shift;
                addForceInc(parseFileArg(optdir, string(argv[i])));
            }
            else if (!strncmp (sw, "-G", strlen("-G"))) {
                addParameter(string(sw+strlen("-G")), false);
            }
            else if (!strcmp(sw, "-gate-stmts") && (i+1)<argc) {
                shift;
                m_gateStmts = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-generate-key")) {
                cout<<protectKeyDefaulted()<<endl;
                exit(0);
            }
            else if (!strcmp(sw, "-getenv") && (i+1)<argc) {
                shift;
                cout<<V3Options::getenvBuiltins(argv[i])<<endl;
                exit(0);
            }
            else if (!strncmp (sw, "-I", 2)) {
                addIncDirUser(parseFileArg(optdir, string(sw+strlen("-I"))));
            }
            else if (!strcmp(sw, "-if-depth") && (i+1)<argc) {
                shift;
                m_ifDepth = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-inline-mult") && (i+1)<argc) {
                shift;
                m_inlineMult = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-LDFLAGS") && (i+1)<argc) {
                shift;
                addLdLibs(argv[i]);
            }
            else if (!strcmp(sw, "-l2-name") && (i+1)<argc) {
                shift;
                m_l2Name = argv[i];
            }
            else if (!strcmp(sw, "-l2name")) {  // Historical and undocumented
                m_l2Name = "v";
            }
            else if (!strcmp(sw, "-make")) {
                shift;
                if (!strcmp(argv[i], "cmake")) {
                    m_cmake = true;
                } else if (!strcmp(argv[i], "gmake")) {
                    m_gmake = true;
                } else {
                    fl->v3fatal("Unknown --make system specified: '"<<argv[i]<<"'");
                }
            }
            else if (!strcmp(sw, "-max-num-width")) {
                shift;
                m_maxNumWidth = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-no-l2name")) {  // Historical and undocumented
                m_l2Name = "";
            }
            else if ((!strcmp(sw, "-language") && (i+1)<argc)
                     || (!strcmp(sw, "-default-language") && (i+1)<argc)) {
                shift;
                V3LangCode optval = V3LangCode(argv[i]);
                if (optval.legal()) {
                    m_defaultLanguage = optval;
                } else {
                    fl->v3fatal("Unknown language specified: "<<argv[i]);
                }
            }
            else if (!strcmp(sw, "-Mdir") && (i+1)<argc) {
                shift; m_makeDir = argv[i];
                addIncDirFallback(m_makeDir);  // Need to find generated files there too
            }
            else if (!strcmp(sw, "-o") && (i+1)<argc) {
                shift; m_exeName = argv[i];
            }
            else if (!strcmp(sw, "-output-split") && (i+1)<argc) {
                shift;
                m_outputSplit = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-output-split-cfuncs") && (i+1)<argc) {
                shift;
                m_outputSplitCFuncs = atoi(argv[i]);
                if (m_outputSplitCFuncs && (!m_outputSplitCTrace
                                            || m_outputSplitCTrace>m_outputSplitCFuncs)) {
                    m_outputSplitCTrace = m_outputSplitCFuncs;
                }
            }
            else if (!strcmp(sw, "-output-split-ctrace")) {  // Undocumented optimization tweak
                shift;
                m_outputSplitCTrace = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-protect-lib") && (i+1)<argc) {
                shift; m_protectLib = argv[i];
                m_protectIds = true;
            }
            else if (!strcmp(sw, "-trace-fst")) {
                m_trace = true;
                m_traceFormat = TraceFormat::FST;
                addLdLibs("-lz");
            }
            else if (!strcmp(sw, "-trace-fst-thread")) {
                m_trace = true;
                m_traceFormat = TraceFormat::FST_THREAD;
                addLdLibs("-lz");
            }
            else if (!strcmp(sw, "-trace-depth") && (i+1)<argc) {
                shift;
                m_traceDepth = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-trace-max-array") && (i+1)<argc) {
                shift;
                m_traceMaxArray = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-trace-max-width") && (i+1)<argc) {
                shift;
                m_traceMaxWidth = atoi(argv[i]);
            }
            else if (!strncmp (sw, "-U", 2)) {
                V3PreShell::undef(string(sw+strlen("-U")));
            }
            else if (!strcmp(sw, "-unroll-count")) {  // Undocumented optimization tweak
                shift;
                m_unrollCount = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-unroll-stmts")) {  // Undocumented optimization tweak
                shift;
                m_unrollStmts = atoi(argv[i]);
            }
            else if (!strcmp(sw, "-v") && (i+1)<argc) {
                shift;
                V3Options::addLibraryFile(parseFileArg(optdir,argv[i]));
            }
            else if (!strcmp(sw, "-clk") && (i+1)<argc) {
                shift;
                V3Options::addClocker(argv[i]);
            }
            else if (!strcmp(sw, "-no-clk") && (i+1)<argc) {
                shift;
                V3Options::addNoClocker(argv[i]);
            }
            else if (!strcmp(sw, "-V")) {
                showVersion(true);
                exit(0);
            }
            else if (!strcmp(sw, "-version")) {
                showVersion(false);
                exit(0);
            }
            else if (!strcmp(sw, "-Wall"))   {
                FileLine::globalWarnLintOff(false);
                FileLine::globalWarnStyleOff(false);
            }
            else if (!strncmp (sw, "-Werror-", strlen("-Werror-")))    {
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
            else if (!strncmp (sw, "-Wfuture-", strlen("-Wfuture-")))  {
                string msg = sw+strlen("-Wfuture-");
                // Note it may not be a future option, but one that is currently implemented.
                addFuture(msg);
            }
            else if (!strncmp (sw, "-Wno-", 5)) {
                if (!strcmp(sw, "-Wno-context")) {
                    m_context = false;
                }
                else if (!strcmp(sw, "-Wno-fatal")) {
                    V3Error::warnFatal(false);
                }
                else if (!strcmp(sw, "-Wno-lint")) {
                    FileLine::globalWarnLintOff(true);
                    FileLine::globalWarnStyleOff(true);
                }
                else if (!strcmp(sw, "-Wno-style")) {
                    FileLine::globalWarnStyleOff(true);
                }
                else {
                    string msg = sw+strlen("-Wno-");
                    if (!(FileLine::globalWarnOff(msg, true))) {
                        fl->v3fatal("Unknown warning specified: "<<sw);
                    }
                }
            }
            else if (!strncmp (sw, "-Wwarn-", 5)) {
                if (!strcmp(sw, "-Wwarn-lint")) {
                    FileLine::globalWarnLintOff(false);
                }
                else if (!strcmp(sw, "-Wwarn-style")) {
                    FileLine::globalWarnStyleOff(false);
                }
                else {
                    string msg = sw+strlen("-Wwarn-");
                    V3ErrorCode code (msg.c_str());
                    if (code == V3ErrorCode::EC_ERROR) {
                        if (!isFuture(msg)) {
                            fl->v3fatal("Unknown warning specified: "<<sw);
                        }
                    } else {
                        FileLine::globalWarnOff(code, false);
                        V3Error::pretendError(code, false);
                    }
                }
            }
            else if (!strcmp(sw, "-bin") && (i+1)<argc) {
                shift; m_bin = argv[i];
            }
            else if (!strcmp(sw, "-compiler") && (i+1)<argc) {
                shift;
                if (!strcmp(argv[i], "clang")) {
                    m_compLimitBlocks = 80;  // limit unknown
                    m_compLimitMembers = 64;  // soft limit, has slowdown bug as of clang++ 3.8
                    m_compLimitParens = 80;  // limit unknown
                } else if (!strcmp(argv[i], "gcc")) {
                    m_compLimitBlocks = 0;  // Bug free
                    m_compLimitMembers = 64;  // soft limit, has slowdown bug as of g++ 7.1
                    m_compLimitParens = 0;  // Bug free
                } else if (!strcmp(argv[i], "msvc")) {
                    m_compLimitBlocks = 80;  // 128, but allow some room
                    m_compLimitMembers = 0;  // probably ok, and AFAIK doesn't support anon structs
                    m_compLimitParens = 80;  // 128, but allow some room
                } else {
                    fl->v3fatal("Unknown setting for --compiler: "<<argv[i]);
                }
            }
            else if (!strcmp(sw, "-F") && (i+1)<argc) {
                shift;
                parseOptsFile(fl, parseFileArg(optdir, argv[i]), true);
            }
            else if (!strcmp(sw, "-f") && (i+1)<argc) {
                shift;
                parseOptsFile(fl, parseFileArg(optdir, argv[i]), false);
            }
            else if (!strcmp(sw, "-gdb")) {
                // Used only in perl shell
            }
            else if (!strcmp(sw, "-rr")) {
                // Used only in perl shell
            }
            else if (!strcmp(sw, "-gdbbt")) {
                // Used only in perl shell
            }
            else if (!strcmp(sw, "-quiet-exit")) {
                // Used only in perl shell
            }
            else if (!strcmp(sw, "-mod-prefix") && (i+1)<argc) {
                shift; m_modPrefix = argv[i];
            }
            else if (!strcmp(sw, "-pins-bv") && (i+1)<argc) {
                shift; m_pinsBv = atoi(argv[i]);
                if (m_pinsBv > 65) fl->v3fatal("--pins-bv maximum is 65: "<<argv[i]);
            }
            else if (!strcmp(sw, "-pipe-filter") && (i+1)<argc) {
                shift; m_pipeFilter = argv[i];
            }
            else if (!strcmp(sw, "-prefix") && (i+1)<argc) {
                shift; m_prefix = argv[i];
                if (m_modPrefix=="") m_modPrefix = m_prefix;
            }
            else if (!strcmp(sw, "-protect-key") && (i+1)<argc) {
                shift; m_protectKey = argv[i];
            }
            else if (!strcmp(sw, "-no-threads")) { m_threads = 0; }  // Undocumented until functional
            else if (!strcmp(sw, "-threads") && (i+1)<argc) {  // Undocumented until functional
                shift; m_threads = atoi(argv[i]);
                if (m_threads < 0) fl->v3fatal("--threads must be >= 0: "<<argv[i]);
            }
            else if (!strcmp(sw, "-threads-dpi") && (i+1)<argc) {
                shift;
                if (!strcmp(argv[i], "all")) {
                    m_threadsDpiPure = true; m_threadsDpiUnpure = true;
                } else if (!strcmp(argv[i], "none")) {
                    m_threadsDpiPure = false; m_threadsDpiUnpure = false;
                } else if (!strcmp(argv[i], "pure")) {
                    m_threadsDpiPure = true; m_threadsDpiUnpure = false;
                } else {
                    fl->v3fatal("Unknown setting for --threads-dpi: "<<argv[i]);
                }
            }
            else if (!strcmp(sw, "-threads-max-mtasks")) {
                shift; m_threadsMaxMTasks = atoi(argv[i]);
                if (m_threadsMaxMTasks < 1)
                    fl->v3fatal("--threads-max-mtasks must be >= 1: "<<argv[i]);
            }
            else if (!strcmp(sw, "-top-module") && (i+1)<argc) {
                shift; m_topModule = argv[i];
            }
            else if (!strcmp(sw, "-unused-regexp") && (i+1)<argc) {
                shift; m_unusedRegexp = argv[i];
            }
            else if (!strcmp(sw, "-x-assign") && (i+1)<argc) {
                shift;
                if (!strcmp(argv[i], "0")) { m_xAssign = "0"; }
                else if (!strcmp(argv[i], "1")) { m_xAssign = "1"; }
                else if (!strcmp(argv[i], "fast")) { m_xAssign = "fast"; }
                else if (!strcmp(argv[i], "unique")) { m_xAssign = "unique"; }
                else {
                    fl->v3fatal("Unknown setting for --x-assign: "<<argv[i]);
                }
            }
            else if (!strcmp(sw, "-x-initial") && (i+1)<argc) {
                shift;
                if (!strcmp(argv[i], "0")) { m_xInitial = "0"; }
                else if (!strcmp(argv[i], "fast")) { m_xInitial = "fast"; }
                else if (!strcmp(argv[i], "unique")) { m_xInitial = "unique"; }
                else {
                    fl->v3fatal("Unknown setting for --x-initial: "<<argv[i]);
                }
            }
            else if (!strcmp(sw, "-xml-output") && (i+1)<argc) {
                shift; m_xmlOutput = argv[i];
                m_xmlOnly = true;
            }
            else if (!strcmp(sw, "-y") && (i+1)<argc) {
                shift; addIncDirUser(parseFileArg(optdir, string(argv[i])));
            }
            else {
                fl->v3fatal("Invalid Option: "<<argv[i]);
            }
            shift;
        }  // - options
        else {
            // Filename
            string filename = parseFileArg(optdir, argv[i]);
            if (suffixed(filename, ".cpp")
                || suffixed(filename, ".cxx")
                || suffixed(filename, ".cc")
                || suffixed(filename, ".c")
                || suffixed(filename, ".sp")) {
                V3Options::addCppFile(filename);
            }
            else if (suffixed(filename, ".a")
                     || suffixed(filename, ".o")
                     || suffixed(filename, ".so")) {
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

    const vl_unique_ptr<std::ifstream> ifp (V3File::new_ifstream(filename));
    if (ifp->fail()) {
        fl->v3error("Cannot open -f command file: "+filename);
        return;
    }

    string whole_file;
    bool inCmt = false;
    while (!ifp->eof()) {
        string line = V3Os::getline(*ifp);
        // Strip simple comments
        string oline;
        // cppcheck-suppress StlMissingComparison
        char lastch = ' ';
        for (string::const_iterator pos = line.begin(); pos != line.end(); lastch = *pos++) {
            if (inCmt) {
                if (*pos=='*' && *(pos+1)=='/') {
                    inCmt = false;
                    ++pos;
                }
            } else if (*pos=='/' && *(pos+1)=='/'
                       && (pos == line.begin() || isspace(lastch))) {    // But allow /file//path
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

    fl = new FileLine(filename);

    // Split into argument list and process
    // Note we try to respect escaped char, double/simple quoted strings
    // Other simulators don't respect a common syntax...

    // Strip off arguments and parse into words
    std::vector<string> args;

    // Parse file using a state machine, taking into account quoted strings and escaped chars
    enum state {ST_IN_OPTION,
                ST_ESCAPED_CHAR,
                ST_IN_QUOTED_STR,
                ST_IN_DOUBLE_QUOTED_STR};

    state st = ST_IN_OPTION;
    state last_st = ST_IN_OPTION;
    string arg;
    for (string::size_type pos = 0;
         pos < whole_file.length(); ++pos) {
        char curr_char = whole_file[pos];
        switch (st) {
        case ST_IN_OPTION:  // Get all chars up to a white space or a "="
            if (isspace(curr_char)) {  // End of option
                if (!arg.empty()) {  // End of word
                    args.push_back(arg);
                }
                arg = "";
                break;
            }
            if (curr_char == '\\') {  // Escape char, we wait for next char
                last_st = st;  // Memorize current state
                st = ST_ESCAPED_CHAR;
                break;
            }
            if (curr_char == '\'') {  // Find begin of quoted string
                // Examine next char in order to decide between
                // a string or a base specifier for integer literal
                ++pos;
                if (pos < whole_file.length()) curr_char = whole_file[pos];
                if (curr_char == '"') {  // String
                    st = ST_IN_QUOTED_STR;
                } else {  // Base specifier
                    arg += '\'';
                }
                arg +=  curr_char;
                break;
            }
            if (curr_char == '"') {  // Find begin of double quoted string
                // Doesn't insert the quote
                st = ST_IN_DOUBLE_QUOTED_STR;
                break;
            }
            arg += curr_char;
            break;
        case ST_IN_QUOTED_STR:  // Just store all chars inside string
            if (curr_char != '\'') {
                arg += curr_char;
            } else {  // End of quoted string
                st = ST_IN_OPTION;
            }
            break;
        case ST_IN_DOUBLE_QUOTED_STR:  // Take into account escaped chars
            if (curr_char != '"') {
                if (curr_char == '\\') {
                    last_st = st;
                    st = ST_ESCAPED_CHAR;
                } else {
                    arg += curr_char;
                }
            } else {  // End of double quoted string
                st = ST_IN_OPTION;
            }
            break;
        case ST_ESCAPED_CHAR:  // Just add the escaped char
            arg += curr_char;
            st = last_st;
            break;
        }
    }
    if (!arg.empty()) {  // Add last word
        args.push_back(arg);
    }

    // Path
    string optdir = (rel ? V3Os::filenameDir(filename) : ".");

    // Convert to argv style arg list and parse them
    std::vector<char*> argv; argv.reserve(args.size()+1);
    for (std::vector<std::string>::const_iterator it = args.begin(); it != args.end(); ++it) {
        argv.push_back(const_cast<char*>(it->c_str()));
    }
    argv.push_back(NULL); // argv is NULL-terminated
    parseOptsList(fl, optdir, static_cast<int>(argv.size()-1), argv.data());
}

//======================================================================

string V3Options::parseFileArg(const string& optdir, const string& relfilename) {
    string filename = V3Os::filenameSubstitute(relfilename);
    if (optdir != "." && V3Os::filenameIsRel(filename)) {
        filename = optdir + "/" + filename;
    }
    return filename;
}

//======================================================================

//! Utility to see if we have a language extension argument and if so add it.
bool V3Options::parseLangExt(const char* swp,  //!< argument text
                             const char* langswp,  //!< option to match
                             const V3LangCode& lc) {  //!< language code
    int len = strlen(langswp);
    if (!strncmp(swp, langswp, len)) {
        addLangExt(swp + len, lc);
        return true;
    } else {
        return false;
    }
}

//======================================================================

void V3Options::showVersion(bool verbose) {
    cout <<version();
    cout <<endl;
    if (!verbose) return;

    cout <<endl;
    cout << "Copyright 2003-2020 by Wilson Snyder.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout <<endl;
    cout << "See https://verilator.org for documentation\n";

    cout <<endl;
    cout << "Summary of configuration:\n";
    cout << "  Compiled in defaults if not in environment:\n";
    cout << "    SYSTEMC            = " << DEFENV_SYSTEMC<<endl;
    cout << "    SYSTEMC_ARCH       = " << DEFENV_SYSTEMC_ARCH<<endl;
    cout << "    SYSTEMC_INCLUDE    = " << DEFENV_SYSTEMC_INCLUDE<<endl;
    cout << "    SYSTEMC_LIBDIR     = " << DEFENV_SYSTEMC_LIBDIR<<endl;
    cout << "    VERILATOR_ROOT     = " << DEFENV_VERILATOR_ROOT<<endl;

    cout <<endl;
    cout << "Environment:\n";
    cout << "    PERL               = " << V3Os::getenvStr("PERL","")<<endl;
    cout << "    SYSTEMC            = " << V3Os::getenvStr("SYSTEMC","")<<endl;
    cout << "    SYSTEMC_ARCH       = " << V3Os::getenvStr("SYSTEMC_ARCH","")<<endl;
    cout << "    SYSTEMC_INCLUDE    = " << V3Os::getenvStr("SYSTEMC_INCLUDE","")<<endl;
    cout << "    SYSTEMC_LIBDIR     = " << V3Os::getenvStr("SYSTEMC_LIBDIR","")<<endl;
    cout << "    VERILATOR_ROOT     = " << V3Os::getenvStr("VERILATOR_ROOT","")<<endl;
    cout << "    VERILATOR_BIN      = " << V3Os::getenvStr("VERILATOR_BIN","")<<endl;  // wrapper uses this
}

//======================================================================

V3Options::V3Options() {
    m_impp = new V3OptionsImp;

    m_assert = false;
    m_autoflush = false;
    m_bboxSys = false;
    m_bboxUnsup = false;
    m_cdc = false;
    m_cmake = false;
    m_context = true;
    m_coverageLine = false;
    m_coverageToggle = false;
    m_coverageUnderscore = false;
    m_coverageUser = false;
    m_debugCheck = false;
    m_debugCollision = false;
    m_debugLeak = true;
    m_debugNondeterminism = false;
    m_debugPartition = false;
    m_debugProtect = false;
    m_debugSelfTest = false;
    m_decoration = true;
    m_dpiHdrOnly = false;
    m_dumpDefines = false;
    m_exe = false;
    m_ignc = false;
    m_inhibitSim = false;
    m_lintOnly = false;
    m_gmake = false;
    m_makePhony = false;
    m_orderClockDly = true;
    m_outFormatOk = false;
    m_pedantic = false;
    m_pinsBv = 65;
    m_pinsScUint = false;
    m_pinsScBigUint = false;
    m_pinsUint8 = false;
    m_ppComments = false;
    m_profCFuncs = false;
    m_profThreads = false;
    m_protectIds = false;
    m_preprocOnly = false;
    m_preprocNoLine = false;
    m_public = false;
    m_publicFlatRW = false;
    m_quietExit = false;
    m_relativeCFuncs = true;
    m_relativeIncludes = false;
    m_reportUnoptflat = false;
    m_savable = false;
    m_stats = false;
    m_statsVars = false;
    m_structsPacked = true;
    m_systemC = false;
    m_threads = 0;
    m_threadsDpiPure = true;
    m_threadsDpiUnpure = false;
    m_threadsCoarsen = true;
    m_threadsMaxMTasks = 0;
    m_trace = false;
    m_traceCoverage = false;
    m_traceDups = false;
    m_traceFormat = TraceFormat::VCD;
    m_traceParams = true;
    m_traceStructs = false;
    m_traceUnderscore = false;
    m_underlineZero = false;
    m_vpi = false;
    m_xInitialEdge = false;
    m_xmlOnly = false;

    m_convergeLimit = 100;
    m_dumpTree = 0;
    m_gateStmts = 100;
    m_ifDepth = 0;
    m_inlineMult = 2000;
    m_maxNumWidth = 65536;
    m_moduleRecursion = 100;
    m_outputSplit = 0;
    m_outputSplitCFuncs = 0;
    m_outputSplitCTrace = 0;
    m_traceDepth = 0;
    m_traceMaxArray = 32;
    m_traceMaxWidth = 256;
    m_unrollCount = 64;
    m_unrollStmts = 30000;

    m_compLimitBlocks = 0;
    m_compLimitMembers = 64;
    m_compLimitParens = 0;

    m_makeDir = "obj_dir";
    m_bin = "";
    m_flags = "";
    m_l2Name = "";
    m_unusedRegexp = "*unused*";
    m_xAssign = "fast";

    m_defaultLanguage = V3LangCode::mostRecent();

    VName::maxLength(128);  // Linux filename limits 256; leave half for prefix

    optimize(1);
    // Default +libext+
    addLibExtV("");  // So include "filename.v" will find the same file
    addLibExtV(".v");
    addLibExtV(".sv");
    // Default -I
    addIncDirFallback(".");  // Looks better than {long_cwd_path}/...
}

V3Options::~V3Options() {
    VL_DO_CLEAR(delete m_impp, m_impp = NULL);
}

void V3Options::setDebugMode(int level) {
    V3Error::debugDefault(level);
    if (!m_dumpTree) m_dumpTree = 3;  // Don't override if already set.
    m_stats = true;
    m_debugCheck = true;
    cout << "Starting "<<version()<<endl;
}

void V3Options::setDebugSrcLevel(const string& srcfile, int level) {
    DebugSrcMap::iterator iter = m_debugSrcs.find(srcfile);
    if (iter!=m_debugSrcs.end()) {
        iter->second = level;
    } else {
        m_debugSrcs.insert(make_pair(srcfile, level));
    }
}

int V3Options::debugSrcLevel(const string& srcfile_path, int default_level) {
    // For simplicity, calling functions can just use __FILE__ for srcfile.
    // That means though we need to cleanup the filename from ../Foo.cpp -> Foo
    string srcfile = V3Os::filenameNonDirExt(srcfile_path);
    DebugSrcMap::iterator iter = m_debugSrcs.find(srcfile);
    if (iter!=m_debugSrcs.end()) {
        return iter->second;
    } else {
        return default_level;
    }
}

void V3Options::setDumpTreeLevel(const string& srcfile, int level) {
    DebugSrcMap::iterator iter = m_dumpTrees.find(srcfile);
    if (iter!=m_dumpTrees.end()) {
        iter->second = level;
    } else {
        m_dumpTrees.insert(make_pair(srcfile, level));
    }
}

int V3Options::dumpTreeLevel(const string& srcfile_path) {
    // For simplicity, calling functions can just use __FILE__ for srcfile.
    // That means though we need to cleanup the filename from ../Foo.cpp -> Foo
    string srcfile = V3Os::filenameNonDirExt(srcfile_path);
    DebugSrcMap::iterator iter = m_dumpTrees.find(srcfile);
    if (iter!=m_dumpTrees.end()) {
        return iter->second;
    } else {
        return m_dumpTree;
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
    m_oGate = flag;
    m_oInline = flag;
    m_oLife = flag;
    m_oLifePost = flag;
    m_oLocalize = flag;
    m_oReloop = flag;
    m_oReorder = flag;
    m_oSplit = flag;
    m_oSubst = flag;
    m_oSubstConst = flag;
    m_oTable = flag;
    m_oDedupe = flag;
    m_oAssemble = flag;
    // And set specific optimization levels
    if (level >= 3) {
        m_inlineMult = -1;  // Maximum inlining
    }
}
