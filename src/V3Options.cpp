// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Options.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3OptionParser.h"
#include "V3Os.h"
#include "V3PreShell.h"
#include "V3String.h"

// clang-format off
#include <sys/types.h>
#include <sys/stat.h>
#ifndef _WIN32
# include <sys/utsname.h>
#endif
#include <algorithm>
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
// clang-format on

//######################################################################
// V3 Internal state

class V3OptionsImp final {
public:
    // TYPES
    using DirMap = std::map<const string, std::set<std::string>>;  // Directory listing

    // STATE
    std::list<string> m_allArgs;  // List of every argument encountered
    std::list<string> m_incDirUsers;  // Include directories (ordered)
    std::set<string> m_incDirUserSet;  // Include directories (for removing duplicates)
    std::list<string> m_incDirFallbacks;  // Include directories (ordered)
    std::set<string> m_incDirFallbackSet;  // Include directories (for removing duplicates)
    std::map<const string, V3LangCode> m_langExts;  // Language extension map
    std::list<string> m_libExtVs;  // Library extensions (ordered)
    std::set<string> m_libExtVSet;  // Library extensions (for removing duplicates)
    DirMap m_dirMap;  // Directory listing

    // ACCESSOR METHODS
    void addIncDirUser(const string& incdir) {
        if (m_incDirUserSet.find(incdir) == m_incDirUserSet.end()) {
            // cppcheck-suppress stlFindInsert  // cppcheck 1.90 bug
            m_incDirUserSet.insert(incdir);
            m_incDirUsers.push_back(incdir);
            m_incDirFallbacks.remove(incdir);  // User has priority over Fallback
            m_incDirFallbackSet.erase(incdir);  // User has priority over Fallback
        }
    }
    void addIncDirFallback(const string& incdir) {
        if (m_incDirUserSet.find(incdir)
            == m_incDirUserSet.end()) {  // User has priority over Fallback
            if (m_incDirFallbackSet.find(incdir) == m_incDirFallbackSet.end()) {
                // cppcheck-suppress stlFindInsert  // cppcheck 1.90 bug
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
            // cppcheck-suppress stlFindInsert  // cppcheck 1.90 bug
            m_libExtVSet.insert(libext);
            m_libExtVs.push_back(libext);
        }
    }
    V3OptionsImp() = default;
    ~V3OptionsImp() = default;
};

//######################################################################
// V3LangCode class functions

V3LangCode::V3LangCode(const char* textp) {
    // Return code for given string, or ERROR, which is a bad code
    for (int codei = V3LangCode::L_ERROR; codei < V3LangCode::_ENUM_END; ++codei) {
        const V3LangCode code = V3LangCode(codei);
        if (0 == VL_STRCASECMP(textp, code.ascii())) {
            m_e = code;
            return;
        }
    }
    m_e = V3LangCode::L_ERROR;
}

//######################################################################
// VTimescale class functions

VTimescale::VTimescale(const string& value, bool& badr)
    : m_e{VTimescale::NONE} {
    badr = true;
    const string spaceless = VString::removeWhitespace(value);
    for (int i = TS_100S; i < _ENUM_END; ++i) {
        const VTimescale ts(i);
        if (spaceless == ts.ascii()) {
            badr = false;
            m_e = ts.m_e;
            break;
        }
    }
}

//######################################################################
// V3HierarchicalBlockOption class functions

// Parse "--hierarchical-block orig_name,mangled_name,param0_name,param0_value,... " option.
// The format of value is as same as -G option. (can be string literal surrounded by ")
V3HierarchicalBlockOption::V3HierarchicalBlockOption(const string& opts) {
    V3StringList vals;
    bool inStr = false;
    string cur;
    static const string hierBlock("--hierarchical-block");
    FileLine cmdfl(FileLine::commandLineFilename());
    // Split by ','. If ',' appears between "", that is not a separator.
    for (string::const_iterator it = opts.begin(); it != opts.end();) {
        if (inStr) {
            if (*it == '\\') {
                ++it;
                if (it == opts.end()) {
                    cmdfl.v3error(hierBlock + " must not end with \\");
                    break;
                }
                if (*it != '"' && *it != '\\') {
                    cmdfl.v3error(hierBlock + " does not allow '" + *it + "' after \\");
                    break;
                }
                cur.push_back(*it);
                ++it;
            } else if (*it == '"') {  // end of string
                cur.push_back(*it);
                vals.push_back(cur);
                cur.clear();
                ++it;
                if (it != opts.end()) {
                    if (*it != ',') {
                        cmdfl.v3error(hierBlock + " expects ',', but '" + *it + "' is passed");
                        break;
                    }
                    ++it;
                    if (it == opts.end()) {
                        cmdfl.v3error(hierBlock + " must not end with ','");
                        break;
                    }
                    inStr = *it == '"';
                    cur.push_back(*it);
                    ++it;
                }
            } else {
                cur.push_back(*it);
                ++it;
            }
        } else {
            if (*it == '"') {
                cmdfl.v3error(hierBlock + " does not allow '\"' in the middle of literal");
                break;
            }
            if (*it == ',') {  // end of this parameter
                vals.push_back(cur);
                cur.clear();
                ++it;
                if (it == opts.end()) {
                    cmdfl.v3error(hierBlock + " must not end with ','");
                    break;
                }
                inStr = *it == '"';
            }
            cur.push_back(*it);
            ++it;
        }
    }
    if (!cur.empty()) vals.push_back(cur);
    if (vals.size() >= 2) {
        if (vals.size() % 2) {
            cmdfl.v3error(hierBlock + " requires the number of entries to be even");
        }
        m_origName = vals[0];
        m_mangledName = vals[1];
    } else {
        cmdfl.v3error(hierBlock + " requires at least two comma-separated values");
    }
    for (size_t i = 2; i + 1 < vals.size(); i += 2) {
        const bool inserted = m_parameters.insert(std::make_pair(vals[i], vals[i + 1])).second;
        if (!inserted) {
            cmdfl.v3error("Module name '" + vals[i] + "' is duplicated in " + hierBlock);
        }
    }
}

//######################################################################
// V3Options class functions

void VTimescale::parseSlashed(FileLine* fl, const char* textp, VTimescale& unitr,
                              VTimescale& precr, bool allowEmpty) {
    // Parse `timescale of <number><units> / <number><units>
    unitr = VTimescale::NONE;
    precr = VTimescale::NONE;

    const char* cp = textp;
    for (; isspace(*cp); ++cp) {}
    const char* const unitp = cp;
    for (; *cp && *cp != '/'; ++cp) {}
    const string unitStr(unitp, cp - unitp);
    for (; isspace(*cp); ++cp) {}
    string precStr;
    if (*cp == '/') {
        ++cp;
        for (; isspace(*cp); ++cp) {}
        const char* const precp = cp;
        for (; *cp && *cp != '/'; ++cp) {}
        precStr = string(precp, cp - precp);
    }
    for (; isspace(*cp); ++cp) {}
    if (*cp) {
        fl->v3error("`timescale syntax error: '" << textp << "'");
        return;
    }

    bool unitbad;
    const VTimescale unit(unitStr, unitbad /*ref*/);
    if (unitbad && !(unitStr.empty() && allowEmpty)) {
        fl->v3error("`timescale timeunit syntax error: '" << unitStr << "'");
        return;
    }
    unitr = unit;

    if (!precStr.empty()) {
        VTimescale prec(VTimescale::NONE);
        bool precbad;
        prec = VTimescale(precStr, precbad /*ref*/);
        if (precbad) {
            fl->v3error("`timescale timeprecision syntax error: '" << precStr << "'");
            return;
        }
        if (!unit.isNone() && !prec.isNone() && unit < prec) {
            fl->v3error("`timescale timeunit '"
                        << unitStr << "' must be greater than or equal to timeprecision '"
                        << precStr << "'");
            return;
        }
        precr = prec;
    }
}

//######################################################################
// V3Options class functions

void V3Options::addIncDirUser(const string& incdir) { m_impp->addIncDirUser(incdir); }
void V3Options::addIncDirFallback(const string& incdir) { m_impp->addIncDirFallback(incdir); }
void V3Options::addLangExt(const string& langext, const V3LangCode& lc) {
    m_impp->addLangExt(langext, lc);
}
void V3Options::addLibExtV(const string& libext) { m_impp->addLibExtV(libext); }
void V3Options::addDefine(const string& defline, bool allowPlus) {
    // Split +define+foo=value into the appropriate parts and parse
    // Optional + says to allow multiple defines on the line
    // + is not quotable, as other simulators do not allow that
    string left = defline;
    while (left != "") {
        string def = left;
        string::size_type pos;
        if (allowPlus && ((pos = left.find('+')) != string::npos)) {
            left = left.substr(pos + 1);
            def.erase(pos);
        } else {
            left = "";
        }
        string value;
        if ((pos = def.find('=')) != string::npos) {
            value = def.substr(pos + 1);
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
            left = left.substr(pos + 1);
            param.erase(pos);
        } else {
            left = "";
        }
        string value;
        if ((pos = param.find('=')) != string::npos) {
            value = param.substr(pos + 1);
            param.erase(pos);
        }
        UINFO(4, "Add parameter" << param << "=" << value << endl);
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
        for (const auto& i : m_parameters) msg << " " << i.first;
        v3error(msg.str());
    }
}

void V3Options::addCppFile(const string& filename) { m_cppFiles.insert(filename); }
void V3Options::addCFlags(const string& filename) { m_cFlags.push_back(filename); }
void V3Options::addLdLibs(const string& filename) { m_ldLibs.push_back(filename); }
void V3Options::addMakeFlags(const string& filename) { m_makeFlags.push_back(filename); }
void V3Options::addFuture(const string& flag) { m_futures.insert(flag); }
void V3Options::addFuture0(const string& flag) { m_future0s.insert(flag); }
void V3Options::addFuture1(const string& flag) { m_future1s.insert(flag); }
bool V3Options::isFuture(const string& flag) const {
    return m_futures.find(flag) != m_futures.end();
}
bool V3Options::isFuture0(const string& flag) const {
    return m_future0s.find(flag) != m_future0s.end();
}
bool V3Options::isFuture1(const string& flag) const {
    return m_future1s.find(flag) != m_future1s.end();
}
bool V3Options::isLibraryFile(const string& filename) const {
    return m_libraryFiles.find(filename) != m_libraryFiles.end();
}
void V3Options::addLibraryFile(const string& filename) { m_libraryFiles.insert(filename); }
bool V3Options::isClocker(const string& signame) const {
    return m_clockers.find(signame) != m_clockers.end();
}
void V3Options::addClocker(const string& signame) { m_clockers.insert(signame); }
bool V3Options::isNoClocker(const string& signame) const {
    return m_noClockers.find(signame) != m_noClockers.end();
}
void V3Options::addNoClocker(const string& signame) { m_noClockers.insert(signame); }
void V3Options::addVFile(const string& filename) {
    // We use a list for v files, because it's legal to have includes
    // in a specific order and multiple of them.
    m_vFiles.push_back(filename);
}
void V3Options::addForceInc(const string& filename) { m_forceIncs.push_back(filename); }

void V3Options::addArg(const string& arg) { m_impp->m_allArgs.push_back(arg); }

string V3Options::allArgsString() const {
    string out;
    for (const string& i : m_impp->m_allArgs) {
        if (out != "") out += " ";
        out += i;
    }
    return out;
}

// Delete some options for Verilation of the hierarchical blocks.
string V3Options::allArgsStringForHierBlock(bool forTop) const {
    std::set<string> vFiles;
    for (const auto& vFile : m_vFiles) vFiles.insert(vFile);
    string out;
    for (std::list<string>::const_iterator it = m_impp->m_allArgs.begin();
         it != m_impp->m_allArgs.end(); ++it) {
        int skip = 0;
        if (it->length() >= 2 && (*it)[0] == '-' && (*it)[1] == '-') {
            skip = 2;
        } else if (it->length() >= 1 && (*it)[0] == '-') {
            skip = 1;
        }
        if (skip > 0) {  // *it is an option
            const string opt = it->substr(skip);  // Remove '-' in the beginning
            const int numStrip = stripOptionsForChildRun(opt, forTop);
            if (numStrip) {
                UASSERT(0 <= numStrip && numStrip <= 2, "should be one of 0, 1, 2");
                if (numStrip == 2) ++it;
                continue;
            }
        } else {  // Not an option
            if (vFiles.find(*it) != vFiles.end()  // Remove HDL
                || m_cppFiles.find(*it) != m_cppFiles.end()) {  // Remove C++
                continue;
            }
        }
        if (out != "") out += " ";
        // Don't use opt here because '-' is removed in it
        // Use double quote because *it may contain whitespaces
        out += '"' + VString::quoteAny(*it, '"', '\\') + '"';
    }
    return out;
}

//######################################################################
// File searching

bool V3Options::fileStatNormal(const string& filename) {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    struct stat sstat;  // Stat information
    const int err = stat(filename.c_str(), &sstat);
    if (err != 0) return false;
    if (S_ISDIR(sstat.st_mode)) return false;
    return true;
}

void V3Options::fileNfsFlush(const string& filename) {
    // NFS caches stat() calls so to get up-to-date information must
    // do a open or opendir on the filename.
    // Faster to just try both rather than check if a file is a dir.
    if (DIR* const dirp = opendir(filename.c_str())) {  // LCOV_EXCL_BR_LINE
        closedir(dirp);  // LCOV_EXCL_LINE
    } else if (int fd = ::open(filename.c_str(), O_RDONLY)) {  // LCOV_EXCL_BR_LINE
        if (fd > 0) ::close(fd);
    }
}

string V3Options::fileExists(const string& filename) {
    // Surprisingly, for VCS and other simulators, this process
    // is quite slow; presumably because of re-reading each directory
    // many times.  So we read a whole dir at once and cache it

    const string dir = V3Os::filenameDir(filename);
    const string basename = V3Os::filenameNonDir(filename);

    auto diriter = m_impp->m_dirMap.find(dir);
    if (diriter == m_impp->m_dirMap.end()) {
        // Read the listing
        m_impp->m_dirMap.emplace(dir, std::set<string>());
        diriter = m_impp->m_dirMap.find(dir);

        std::set<string>* setp = &(diriter->second);

        if (DIR* const dirp = opendir(dir.c_str())) {
            while (struct dirent* direntp = readdir(dirp)) setp->insert(direntp->d_name);
            closedir(dirp);
        }
    }
    // Find it
    const std::set<string>* filesetp = &(diriter->second);
    const auto fileiter = filesetp->find(basename);
    if (fileiter == filesetp->end()) {
        return "";  // Not found
    }
    // Check if it is a directory, ignore if so
    string filenameOut = V3Os::filenameFromDirBase(dir, basename);
    if (!fileStatNormal(filenameOut)) return "";  // Directory
    return filenameOut;
}

string V3Options::filePathCheckOneDir(const string& modname, const string& dirname) {
    for (const string& i : m_impp->m_libExtVs) {
        const string fn = V3Os::filenameFromDirBase(dirname, modname + i);
        string exists = fileExists(fn);
        if (exists != "") {
            // Strip ./, it just looks ugly
            if (exists.substr(0, 2) == "./") exists.erase(0, 2);
            return exists;
        }
    }
    return "";
}

// Checks if a option needs to be stripped for child run of hierarchical Verilation.
// 0: Keep the option including its argument
// 1: Delete the option which has no argument
// 2: Delete the option and its argument
int V3Options::stripOptionsForChildRun(const string& opt, bool forTop) {
    if (opt == "Mdir" || opt == "clk" || opt == "lib-create" || opt == "f" || opt == "j"
        || opt == "l2-name" || opt == "mod-prefix" || opt == "prefix" || opt == "protect-lib"
        || opt == "protect-key" || opt == "threads" || opt == "top-module" || opt == "v") {
        return 2;
    }
    if (opt == "build" || (!forTop && (opt == "cc" || opt == "exe" || opt == "sc"))
        || opt == "hierarchical" || (opt.length() > 2 && opt.substr(0, 2) == "G=")) {
        return 1;
    }
    return 0;
}

string V3Options::filePath(FileLine* fl, const string& modname, const string& lastpath,
                           const string& errmsg) {  // Error prefix or "" to suppress error
    // Find a filename to read the specified module name,
    // using the incdir and libext's.
    // Return "" if not found.
    for (const string& dir : m_impp->m_incDirUsers) {
        string exists = filePathCheckOneDir(modname, dir);
        if (exists != "") return exists;
    }
    for (const string& dir : m_impp->m_incDirFallbacks) {
        string exists = filePathCheckOneDir(modname, dir);
        if (exists != "") return exists;
    }

    if (m_relativeIncludes) {
        const string exists = filePathCheckOneDir(modname, lastpath);
        if (exists != "") return V3Os::filenameRealPath(exists);
    }

    // Warn and return not found
    if (errmsg != "") {
        fl->v3error(errmsg + modname);
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
            fl->v3error("This may be because there's no search path specified with -I<dir>.");
        }
        std::cerr << V3Error::warnMore() << "... Looked in:" << endl;
        for (const string& dir : m_impp->m_incDirUsers) {
            for (const string& ext : m_impp->m_libExtVs) {
                const string fn = V3Os::filenameFromDirBase(dir, modname + ext);
                std::cerr << V3Error::warnMore() << "     " << fn << endl;
            }
        }
        for (const string& dir : m_impp->m_incDirFallbacks) {
            for (const string& ext : m_impp->m_libExtVs) {
                const string fn = V3Os::filenameFromDirBase(dir, modname + ext);
                std::cerr << V3Error::warnMore() << "     " << fn << endl;
            }
        }
    }
}

//! Determine what language is associated with a filename

//! If we recognize the extension, use its language, otherwise, use the
//! default language.
V3LangCode V3Options::fileLanguage(const string& filename) {
    string ext = V3Os::filenameNonDir(filename);
    string::size_type pos;
    if ((pos = ext.rfind('.')) != string::npos) {
        ext.erase(0, pos + 1);
        const auto it = m_impp->m_langExts.find(ext);
        if (it != m_impp->m_langExts.end()) return it->second;
    }
    return m_defaultLanguage;
}

//######################################################################
// Environment

string V3Options::getenvBuiltins(const string& var) {
    if (var == "MAKE") {
        return getenvMAKE();
    } else if (var == "PERL") {
        return getenvPERL();
    } else if (var == "SYSTEMC") {
        return getenvSYSTEMC();
    } else if (var == "SYSTEMC_ARCH") {
        return getenvSYSTEMC_ARCH();
    } else if (var == "SYSTEMC_INCLUDE") {
        return getenvSYSTEMC_INCLUDE();
    } else if (var == "SYSTEMC_LIBDIR") {
        return getenvSYSTEMC_LIBDIR();
    } else if (var == "VERILATOR_ROOT") {
        return getenvVERILATOR_ROOT();
    } else {
        return V3Os::getenvStr(var, "");
    }
}

#ifdef __FreeBSD__
string V3Options::getenvMAKE() { return V3Os::getenvStr("MAKE", "gmake"); }
#else
string V3Options::getenvMAKE() { return V3Os::getenvStr("MAKE", "make"); }
#endif

string V3Options::getenvPERL() {  //
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
#if defined(__MINGW32__)
        // Hardcoded with MINGW current version. Would like a better way.
        const string sysname = "MINGW32_NT-5.0";
        var = "mingw32";
#elif defined(_WIN32)
        const string sysname = "WIN32";
        var = "win32";
#else
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
        struct utsname uts;
        uname(&uts);
        const string sysname = VString::downcase(uts.sysname);  // aka  'uname -s'
        if (VL_UNCOVERABLE(VString::wildmatch(sysname.c_str(), "*solaris*"))) {
            var = "gccsparcOS5";
        } else if (VL_UNCOVERABLE(VString::wildmatch(sysname.c_str(), "*cygwin*"))) {
            var = "cygwin";
        } else {
            var = "linux";
        }
#endif
        V3Os::setenvStr("SYSTEMC_ARCH", var, "From sysname '" + sysname + "'");
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
        const string sc = getenvSYSTEMC();
        if (sc != "") var = sc + "/include";
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
        const string sc = getenvSYSTEMC();
        const string arch = getenvSYSTEMC_ARCH();
        if (sc != "" && arch != "") var = sc + "/lib-" + arch;
    }
    return var;
}

string V3Options::getenvVERILATOR_ROOT() {
    string var = V3Os::getenvStr("VERILATOR_ROOT", "");
    if (var == "" && string(DEFENV_VERILATOR_ROOT) != "") {
        var = DEFENV_VERILATOR_ROOT;
        V3Os::setenvStr("VERILATOR_ROOT", var, "Hardcoded at build time");
    }
    if (var == "") v3fatal("$VERILATOR_ROOT needs to be in environment\n");
    return var;
}

bool V3Options::systemCSystemWide() {
#ifdef HAVE_SYSTEMC
    return true;
#else
    return false;
#endif
}

bool V3Options::systemCFound() {
    return (systemCSystemWide()
            || (!getenvSYSTEMC_INCLUDE().empty() && !getenvSYSTEMC_LIBDIR().empty()));
}

//######################################################################
// V3 Options notification methods

void V3Options::notify() {
    FileLine* const cmdfl = new FileLine(FileLine::commandLineFilename());

    // Notify that all arguments have been passed and final modification can be made.
    if (!outFormatOk() && !cdc() && !dpiHdrOnly() && !lintOnly() && !preprocOnly() && !xmlOnly()) {
        v3fatal("verilator: Need --cc, --sc, --cdc, --dpi-hdr-only, --lint-only, "
                "--xml-only or --E option");
    }

    if (cdc()) {
        cmdfl->v3warn(DEPRECATED, "Option --cdc is deprecated and is planned for removal");
    }

    if (m_build && (m_gmake || m_cmake)) {
        cmdfl->v3error("--make cannot be used together with --build. Suggest see manual");
    }

    // Make sure at least one make system is enabled
    if (!m_gmake && !m_cmake) m_gmake = true;

    if (m_hierarchical && (m_hierChild || !m_hierBlocks.empty())) {
        cmdfl->v3error(
            "--hierarchical must not be set with --hierarchical-child or --hierarchical-block");
    }
    if (m_hierChild && m_hierBlocks.empty()) {
        cmdfl->v3error("--hierarchical-block must be set when --hierarchical-child is set");
    }

    if (protectIds()) {
        if (allPublic()) {
            // We always call protect() on names, we don't check if public or not
            // Hence any external references wouldn't be able to find the refed public object.
            cmdfl->v3warn(E_UNSUPPORTED, "Unsupported: Using --protect-ids with --public\n"  //
                                             + V3Error::warnMore()
                                             + "... Suggest remove --public.");
        }
        if (trace()) {
            cmdfl->v3warn(INSECURE,
                          "Using --protect-ids with --trace may expose private design details\n"
                              + V3Error::warnMore() + "... Suggest remove --trace.");
        }
        if (vpi()) {
            cmdfl->v3warn(INSECURE,
                          "Using --protect-ids with --vpi may expose private design details\n"
                              + V3Error::warnMore() + "... Suggest remove --vpi.");
        }
    }

    // Default some options if not turned on or off
    if (v3Global.opt.skipIdentical().isDefault()) {
        v3Global.opt.m_skipIdentical.setTrueOrFalse(  //
            !v3Global.opt.cdc()  //
            && !v3Global.opt.dpiHdrOnly()  //
            && !v3Global.opt.lintOnly()  //
            && !v3Global.opt.preprocOnly()  //
            && !v3Global.opt.xmlOnly());
    }
    if (v3Global.opt.makeDepend().isDefault()) {
        v3Global.opt.m_makeDepend.setTrueOrFalse(  //
            !v3Global.opt.cdc()  //
            && !v3Global.opt.dpiHdrOnly()  //
            && !v3Global.opt.lintOnly()  //
            && !v3Global.opt.preprocOnly()  //
            && !v3Global.opt.xmlOnly());
    }

    if (trace()) {
        // With --trace-fst, --trace-threads implies --threads 1 unless explicitly specified
        if (traceFormat().fst() && traceThreads() && !threads()) m_threads = 1;

        // With --trace, --trace-threads is ignored
        if (traceFormat().vcd()) m_traceThreads = threads() ? 1 : 0;
    }

    UASSERT(!(useTraceParallel() && useTraceOffload()),
            "Cannot use both parallel and offloaded tracing");

    // Default split limits if not specified
    if (m_outputSplitCFuncs < 0) m_outputSplitCFuncs = m_outputSplit;
    if (m_outputSplitCTrace < 0) m_outputSplitCTrace = m_outputSplit;

    if (v3Global.opt.main() && v3Global.opt.systemC()) {
        cmdfl->v3warn(E_UNSUPPORTED,
                      "--main not usable with SystemC. Suggest see examples for sc_main().");
    }

    if (coverage() && savable()) {
        cmdfl->v3error("--coverage and --savable not supported together");
    }

    // Mark options as available
    m_available = true;
}

//######################################################################
// V3 Options accessors

string V3Options::version() {
    string ver = DTVERSION;
    ver += " rev " + cvtToStr(DTVERSION_rev);
    return ver;
}

string V3Options::protectKeyDefaulted() {
    if (m_protectKey.empty()) {
        // Create a key with a human-readable symbol-like name.
        // This conversion drops ~2 bits of entropy out of 256, shouldn't matter.
        VHashSha256 digest(V3Os::trueRandom(32));
        m_protectKey = "VL-KEY-" + digest.digestSymbol();
    }
    return m_protectKey;
}

void V3Options::throwSigsegv() {  // LCOV_EXCL_START
#if !(defined(VL_CPPCHECK) || defined(__clang_analyzer__))
    // clang-format off
    *static_cast<volatile char*>(nullptr) = 0;  // Intentional core dump, ignore warnings here
    // clang-format on
#endif
}  // LCOV_EXCL_STOP

VTimescale V3Options::timeComputePrec(const VTimescale& flag) const {
    if (!timeOverridePrec().isNone()) {
        return timeOverridePrec();
    } else if (flag.isNone()) {
        return timeDefaultPrec();
    } else {
        return flag;
    }
}

VTimescale V3Options::timeComputeUnit(const VTimescale& flag) const {
    if (!timeOverrideUnit().isNone()) {
        return timeOverrideUnit();
    } else if (flag.isNone()) {
        return timeDefaultUnit();
    } else {
        return flag;
    }
}

//######################################################################
// V3 Options utilities

string V3Options::argString(int argc, char** argv) {
    // Return list of arguments as simple string
    string opts;
    for (int i = 0; i < argc; ++i) {
        if (i != 0) opts += " ";
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
        v3fatal("verilator: No Input Verilog file specified on command line, "
                "see verilator --help for more information\n");
    }

    // Default prefix to the filename
    if (prefix() == "" && topModule() != "")
        m_prefix = string("V") + AstNode::encodeName(topModule());
    if (prefix() == "" && vFilesList.size() >= 1)
        m_prefix = string("V") + AstNode::encodeName(V3Os::filenameNonExt(*(vFilesList.begin())));
    if (modPrefix() == "") m_modPrefix = prefix();

    // Find files in makedir
    addIncDirFallback(makeDir());
}

//======================================================================

bool V3Options::suffixed(const string& sw, const char* arg) {
    if (strlen(arg) > sw.length()) return false;
    return (0 == strcmp(sw.c_str() + sw.length() - strlen(arg), arg));
}

void V3Options::parseOptsList(FileLine* fl, const string& optdir, int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
    for (int i = 0; i < argc; ++i) {
        addArg(argv[i]);  // -f's really should be inserted in the middle, but this is for debug
    }

    V3OptionParser parser;
    const V3OptionParser::AppendHelper DECL_OPTION{parser};
    V3OPTION_PARSER_DECL_TAGS;

    const auto callStrSetter = [this](void (V3Options::*cbStr)(const string&)) {
        return [this, cbStr](const string& v) { (this->*cbStr)(v); };
    };
    // Usage
    // DECL_OPTION("-option", action, pointer_or_lambda);
    // action: one of Set, OnOff, CbCall, CbOnOff, CbVal, CbPartialMatch, and CbPartialMatchVal
    //   Set              : Set value to a variable, pointer_or_lambda must be a pointer to the
    //                      variable.
    //                      true is set to bool-ish variable when '-opt' is passed to verilator.
    //                      val is set to int and string variable when '-opt val' is passed.
    //   OnOff            : Set value to a bool-ish variable, pointer_or_lambda must be a pointer
    //                      to bool or VOptionBool.
    //                      true is set if "-opt" is passed to verilator while false is set if
    //                      "-no-opt" is given.
    //   CbCall           : Call lambda or function that does not take argument.
    //   CbOnOff          : Call lambda or function that takes bool argument.
    //                      Supports "-opt" and "-no-opt" style options.
    //   CbVal            : Call lambda or function that takes int or const char*.
    //                      "-opt val" is passed to verilator, val is passed to the lambda.
    //                      If a function to be called is a member of V3Options that only takes
    //                      const string&, callStrSetter(&V3Options::memberFunc) can be passed
    //                      instead of lambda as a syntax sugar.
    //   CbPartialMatch   : Call lambda or function that takes remaining string.
    //                      e.g. DECL_OPTION("-opt-", CbPartialMatch, [](const char*optp) { cout <<
    //                      optp << endl; }); and "-opt-ABC" is passed, "ABC" will be emit to
    //                      stdout.
    //   CbPartialMatchVal: Call lambda or function that takes remaining string and value.
    //                      e.g. DECL_OPTION("-opt-", CbPartialMatchVal, [](const char*optp, const
    //                      char*valp) {
    //                               cout << optp << ":" << valp << endl; });
    //                      and "-opt-ABC VAL" is passed, "ABC:VAL" will be emit to stdout.
    //
    // DECL_OPTION is not C-macro to get correct line coverage even when lambda is passed.
    // (If DECL_OPTION is a macro, then lambda would be collapsed into a single line).

    // Plus options
    DECL_OPTION("+define+", CbPartialMatch, [this](const char* optp) { addDefine(optp, true); });
    DECL_OPTION("+incdir+", CbPartialMatch,
                [this, &optdir](const char* optp) { addIncDirUser(parseFileArg(optdir, optp)); });
    DECL_OPTION("+libext+", CbPartialMatch, [this](const char* optp) {
        string exts = optp;
        string::size_type pos;
        while ((pos = exts.find('+')) != string::npos) {
            addLibExtV(exts.substr(0, pos));
            exts = exts.substr(pos + 1);
        }
        addLibExtV(exts);
    });
    DECL_OPTION("+librescan", CbCall, []() {});  // NOP
    DECL_OPTION("+notimingchecks", CbCall, []() {});  // NOP
    DECL_OPTION("+systemverilogext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1800_2017); });
    DECL_OPTION("+verilog1995ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1364_1995); });
    DECL_OPTION("+verilog2001ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1364_2001); });
    DECL_OPTION("+1364-1995ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1364_1995); });
    DECL_OPTION("+1364-2001ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1364_2001); });
    DECL_OPTION("+1364-2005ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1364_2005); });
    DECL_OPTION("+1800-2005ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1800_2005); });
    DECL_OPTION("+1800-2009ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1800_2009); });
    DECL_OPTION("+1800-2012ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1800_2012); });
    DECL_OPTION("+1800-2017ext+", CbPartialMatch,
                [this](const char* optp) { addLangExt(optp, V3LangCode::L1800_2017); });

    // Minus options
    DECL_OPTION("-assert", OnOff, &m_assert);
    DECL_OPTION("-autoflush", OnOff, &m_autoflush);

    DECL_OPTION("-bbox-sys", OnOff, &m_bboxSys);
    DECL_OPTION("-bbox-unsup", CbOnOff, [this](bool flag) {
        m_bboxUnsup = flag;
        FileLine::globalWarnOff(V3ErrorCode::E_UNSUPPORTED, true);
    });
    DECL_OPTION("-bin", Set, &m_bin);
    DECL_OPTION("-build", Set, &m_build);

    DECL_OPTION("-CFLAGS", CbVal, callStrSetter(&V3Options::addCFlags));
    DECL_OPTION("-cc", CbCall, [this]() {
        m_outFormatOk = true;
        m_systemC = false;
    });
    DECL_OPTION("-cdc", OnOff, &m_cdc);
    DECL_OPTION("-clk", CbVal, callStrSetter(&V3Options::addClocker));
    DECL_OPTION("-no-clk", CbVal, callStrSetter(&V3Options::addNoClocker));
    DECL_OPTION("-comp-limit-blocks", Set, &m_compLimitBlocks).undocumented();
    DECL_OPTION("-comp-limit-members", Set,
                &m_compLimitMembers)
        .undocumented();  // Ideally power-of-two so structs stay aligned
    DECL_OPTION("-comp-limit-parens", Set, &m_compLimitParens).undocumented();
    DECL_OPTION("-comp-limit-syms", CbVal, [](int val) { VName::maxLength(val); }).undocumented();
    DECL_OPTION("-compiler", CbVal, [this, fl](const char* valp) {
        if (!strcmp(valp, "clang")) {
            m_compLimitBlocks = 80;  // limit unknown
            m_compLimitMembers = 64;  // soft limit, has slowdown bug as of clang++ 3.8
            m_compLimitParens = 240;  // controlled by -fbracket-depth, which defaults to 256
        } else if (!strcmp(valp, "gcc")) {
            m_compLimitBlocks = 0;  // Bug free
            m_compLimitMembers = 64;  // soft limit, has slowdown bug as of g++ 7.1
            m_compLimitParens = 240;  // Unlimited, but generate same code as for clang
        } else if (!strcmp(valp, "msvc")) {
            m_compLimitBlocks = 80;  // 128, but allow some room
            m_compLimitMembers = 0;  // probably ok, and AFAIK doesn't support anon structs
            m_compLimitParens = 80;  // 128, but allow some room
        } else {
            fl->v3fatal("Unknown setting for --compiler: '"
                        << valp << "'\n"
                        << fl->warnMore() << "... Suggest 'clang', 'gcc', or 'msvc'");
        }
    });
    DECL_OPTION("-coverage", CbOnOff, [this](bool flag) { coverage(flag); });
    DECL_OPTION("-converge-limit", Set, &m_convergeLimit);
    DECL_OPTION("-coverage-line", OnOff, &m_coverageLine);
    DECL_OPTION("-coverage-max-width", Set, &m_coverageMaxWidth);
    DECL_OPTION("-coverage-toggle", OnOff, &m_coverageToggle);
    DECL_OPTION("-coverage-underscore", OnOff, &m_coverageUnderscore);
    DECL_OPTION("-coverage-user", OnOff, &m_coverageUser);

    DECL_OPTION("-D", CbPartialMatch, [this](const char* valp) { addDefine(valp, false); });
    DECL_OPTION("-debug", CbCall, [this]() { setDebugMode(3); });
    DECL_OPTION("-debugi", CbVal, [this](int v) { setDebugMode(v); });
    DECL_OPTION("-debugi-", CbPartialMatchVal, [this](const char* optp, const char* valp) {
        setDebugSrcLevel(optp, std::atoi(valp));
    });
    DECL_OPTION("-debug-abort", CbCall,
                V3Error::vlAbort)
        .undocumented();  // See also --debug-sigsegv
    DECL_OPTION("-debug-check", OnOff, &m_debugCheck);
    DECL_OPTION("-debug-collision", OnOff, &m_debugCollision).undocumented();
    DECL_OPTION("-debug-emitv", OnOff, &m_debugEmitV).undocumented();
    DECL_OPTION("-debug-exit-parse", OnOff, &m_debugExitParse).undocumented();
    DECL_OPTION("-debug-exit-uvm", OnOff, &m_debugExitUvm).undocumented();
    DECL_OPTION("-debug-fatalsrc", CbCall, []() {
        v3fatalSrc("--debug-fatal-src");
    }).undocumented();  // See also --debug-abort
    DECL_OPTION("-debug-leak", OnOff, &m_debugLeak);
    DECL_OPTION("-debug-nondeterminism", OnOff, &m_debugNondeterminism);
    DECL_OPTION("-debug-partition", OnOff, &m_debugPartition).undocumented();
    DECL_OPTION("-debug-protect", OnOff, &m_debugProtect).undocumented();
    DECL_OPTION("-debug-self-test", OnOff, &m_debugSelfTest).undocumented();
    DECL_OPTION("-debug-sigsegv", CbCall, throwSigsegv).undocumented();  // See also --debug-abort
    DECL_OPTION("-decoration", OnOff, &m_decoration);
    DECL_OPTION("-dpi-hdr-only", OnOff, &m_dpiHdrOnly);
    DECL_OPTION("-dump-defines", OnOff, &m_dumpDefines);
    DECL_OPTION("-dump-tree", CbOnOff,
                [this](bool flag) { m_dumpTree = flag ? 3 : 0; });  // Also see --dump-treei
    DECL_OPTION("-dump-tree-addrids", OnOff, &m_dumpTreeAddrids);
    DECL_OPTION("-dump-treei", Set, &m_dumpTree);
    DECL_OPTION("-dump-treei-", CbPartialMatchVal, [this](const char* optp, const char* valp) {
        setDumpTreeLevel(optp, std::atoi(valp));
    });

    DECL_OPTION("-E", Set, &m_preprocOnly);
    DECL_OPTION("-error-limit", CbVal, static_cast<void (*)(int)>(&V3Error::errorLimit));
    DECL_OPTION("-exe", OnOff, &m_exe);
    DECL_OPTION("-expand-limit", CbVal,
                [this](const char* valp) { m_expandLimit = std::atoi(valp); });

    DECL_OPTION("-F", CbVal, [this, fl, &optdir](const char* valp) {
        parseOptsFile(fl, parseFileArg(optdir, valp), true);
    });
    DECL_OPTION("-FI", CbVal,
                [this, &optdir](const char* valp) { addForceInc(parseFileArg(optdir, valp)); });
    DECL_OPTION("-f", CbVal, [this, fl, &optdir](const char* valp) {
        parseOptsFile(fl, parseFileArg(optdir, valp), false);
    });
    DECL_OPTION("-flatten", OnOff, &m_flatten);
    DECL_OPTION("-future0", CbVal, [this](const char* valp) { addFuture0(valp); });
    DECL_OPTION("-future1", CbVal, [this](const char* valp) { addFuture1(valp); });

    DECL_OPTION("-facyc-simp", FOnOff, &m_fAcycSimp);
    DECL_OPTION("-fassemble", FOnOff, &m_fAssemble);
    DECL_OPTION("-fcase", FOnOff, &m_fCase);
    DECL_OPTION("-fcombine", FOnOff, &m_fCombine);
    DECL_OPTION("-fconst", FOnOff, &m_fConst);
    DECL_OPTION("-fconst-bit-op-tree", FOnOff, &m_fConstBitOpTree);
    DECL_OPTION("-fdedup", FOnOff, &m_fDedupe);
    DECL_OPTION("-fexpand", FOnOff, &m_fExpand);
    DECL_OPTION("-fgate", FOnOff, &m_fGate);
    DECL_OPTION("-finline", FOnOff, &m_fInline);
    DECL_OPTION("-flife", FOnOff, &m_fLife);
    DECL_OPTION("-flife-post", FOnOff, &m_fLifePost);
    DECL_OPTION("-flocalize", FOnOff, &m_fLocalize);
    DECL_OPTION("-fmerge-cond", FOnOff, &m_fMergeCond);
    DECL_OPTION("-fmerge-cond-motion", FOnOff, &m_fMergeCondMotion);
    DECL_OPTION("-fmerge-const-pool", FOnOff, &m_fMergeConstPool);
    DECL_OPTION("-freloop", FOnOff, &m_fReloop);
    DECL_OPTION("-freorder", FOnOff, &m_fReorder);
    DECL_OPTION("-fsplit", FOnOff, &m_fSplit);
    DECL_OPTION("-fsubst", FOnOff, &m_fSubst);
    DECL_OPTION("-fsubst-const", FOnOff, &m_fSubstConst);
    DECL_OPTION("-ftable", FOnOff, &m_fTable);

    DECL_OPTION("-G", CbPartialMatch, [this](const char* optp) { addParameter(optp, false); });
    DECL_OPTION("-gate-stmts", Set, &m_gateStmts);
    DECL_OPTION("-gdb", CbCall, []() {});  // Processed only in bin/verilator shell
    DECL_OPTION("-gdbbt", CbCall, []() {});  // Processed only in bin/verilator shell
    DECL_OPTION("-generate-key", CbCall, [this]() {
        cout << protectKeyDefaulted() << endl;
        std::exit(0);
    });
    DECL_OPTION("-getenv", CbVal, [](const char* valp) {
        cout << V3Options::getenvBuiltins(valp) << endl;
        std::exit(0);
    });

    DECL_OPTION("-hierarchical", OnOff, &m_hierarchical);
    DECL_OPTION("-hierarchical-block", CbVal, [this](const char* valp) {
        const V3HierarchicalBlockOption opt(valp);
        m_hierBlocks.emplace(opt.mangledName(), opt);
    });
    DECL_OPTION("-hierarchical-child", Set, &m_hierChild);

    DECL_OPTION("-I", CbPartialMatch,
                [this, &optdir](const char* optp) { addIncDirUser(parseFileArg(optdir, optp)); });
    DECL_OPTION("-if-depth", Set, &m_ifDepth);
    DECL_OPTION("-ignc", OnOff, &m_ignc);
    DECL_OPTION("-inline-mult", Set, &m_inlineMult);
    DECL_OPTION("-instr-count-dpi", CbVal, [this, fl](int val) {
        m_instrCountDpi = val;
        if (m_instrCountDpi < 0) fl->v3fatal("--instr-count-dpi must be non-negative: " << val);
    });

    DECL_OPTION("-LDFLAGS", CbVal, callStrSetter(&V3Options::addLdLibs));
    const auto setLang = [this, fl](const char* valp) {
        const V3LangCode optval = V3LangCode(valp);
        if (optval.legal()) {
            m_defaultLanguage = optval;
        } else {
            VSpellCheck spell;
            for (int i = V3LangCode::L_ERROR + 1; i < V3LangCode::_ENUM_END; ++i) {
                spell.pushCandidate(V3LangCode{i}.ascii());
            }
            fl->v3fatal("Unknown language specified: " << valp << spell.bestCandidateMsg(valp));
        }
    };
    DECL_OPTION("-default-language", CbVal, setLang);
    DECL_OPTION("-language", CbVal, setLang);
    DECL_OPTION("-lib-create", Set, &m_libCreate);
    DECL_OPTION("-lint-only", OnOff, &m_lintOnly);
    DECL_OPTION("-l2-name", Set, &m_l2Name);
    DECL_OPTION("-no-l2name", CbCall, [this]() { m_l2Name = ""; }).undocumented();  // Historical
    DECL_OPTION("-l2name", CbCall, [this]() { m_l2Name = "v"; }).undocumented();  // Historical

    DECL_OPTION("-MAKEFLAGS", CbVal, callStrSetter(&V3Options::addMakeFlags));
    DECL_OPTION("-MMD", OnOff, &m_makeDepend);
    DECL_OPTION("-MP", OnOff, &m_makePhony);
    DECL_OPTION("-Mdir", CbVal, [this](const char* valp) {
        m_makeDir = valp;
        addIncDirFallback(m_makeDir);  // Need to find generated files there too
    });
    DECL_OPTION("-main", OnOff, &m_main).undocumented();  // Future
    DECL_OPTION("-make", CbVal, [this, fl](const char* valp) {
        if (!strcmp(valp, "cmake")) {
            m_cmake = true;
        } else if (!strcmp(valp, "gmake")) {
            m_gmake = true;
        } else {
            fl->v3fatal("Unknown --make system specified: '" << valp << "'");
        }
    });
    DECL_OPTION("-max-num-width", Set, &m_maxNumWidth);
    DECL_OPTION("-mod-prefix", Set, &m_modPrefix);

    DECL_OPTION("-O0", CbCall, [this]() { optimize(0); });
    DECL_OPTION("-O1", CbCall, [this]() { optimize(1); });
    DECL_OPTION("-O2", CbCall, [this]() { optimize(2); });
    DECL_OPTION("-O3", CbCall, [this]() { optimize(3); });

    DECL_OPTION("-O", CbPartialMatch, [this, fl](const char* optp) {
        // Optimization, e.g. -O1rX
        // LCOV_EXCL_START
        fl->v3warn(DEPRECATED, "Option -O<letter> is deprecated. "
                               "Use -f<optimization> or -fno-<optimization> instead.");
        for (const char* cp = optp; *cp; ++cp) {
            const bool flag = isupper(*cp);
            switch (tolower(*cp)) {
            case '0': optimize(0); break;
            case '1': optimize(1); break;
            case '2': optimize(2); break;
            case '3': optimize(3); break;
            case 'a': m_fTable = flag; break;  // == -fno-table
            case 'b': m_fCombine = flag; break;  // == -fno-combine
            case 'c': m_fConst = flag; break;  // == -fno-const
            case 'd': m_fDedupe = flag; break;  // == -fno-dedup
            case 'e': m_fCase = flag; break;  // == -fno-case
            case 'g': m_fGate = flag; break;  // == -fno-gate
            case 'i': m_fInline = flag; break;  // == -fno-inline
            case 'k': m_fSubstConst = flag; break;  // == -fno-subst-const
            case 'l': m_fLife = flag; break;  // == -fno-life
            case 'm': m_fAssemble = flag; break;  // == -fno-assemble
            case 'o': m_fConstBitOpTree = flag; break;  // == -fno-const-bit-op-tree
            case 'p':
                m_public = !flag;
                break;  // With -Op so flag=0, we want public on so few optimizations done
            case 'r': m_fReorder = flag; break;  // == -fno-reorder
            case 's': m_fSplit = flag; break;  // == -fno-split
            case 't': m_fLifePost = flag; break;  // == -fno-life-post
            case 'u': m_fSubst = flag; break;  // == -fno-subst
            case 'v': m_fReloop = flag; break;  // == -fno-reloop
            case 'w': m_fMergeCond = flag; break;  // == -fno-merge-cond
            case 'x': m_fExpand = flag; break;  // == -fno-expand
            case 'y': m_fAcycSimp = flag; break;  // == -fno-acyc-simp
            case 'z': m_fLocalize = flag; break;  // == -fno-localize
            default:
                break;  // No error, just ignore
                // LCOV_EXCL_STOP
            }
        }
    });
    DECL_OPTION("-o", Set, &m_exeName);
    DECL_OPTION("-order-clock-delay", OnOff, &m_orderClockDly);
    DECL_OPTION("-output-split", Set, &m_outputSplit);
    DECL_OPTION("-output-split-cfuncs", CbVal, [this, fl](const char* valp) {
        m_outputSplitCFuncs = std::atoi(valp);
        if (m_outputSplitCFuncs < 0) {
            fl->v3error("--output-split-cfuncs must be >= 0: " << valp);
        }
    });
    DECL_OPTION("-output-split-ctrace", CbVal, [this, fl](const char* valp) {
        m_outputSplitCTrace = std::atoi(valp);
        if (m_outputSplitCTrace < 0) {
            fl->v3error("--output-split-ctrace must be >= 0: " << valp);
        }
    });

    DECL_OPTION("-P", Set, &m_preprocNoLine);
    DECL_OPTION("-pvalue+", CbPartialMatch,
                [this](const char* varp) { addParameter(varp, false); });
    DECL_OPTION("-pins64", CbCall, [this]() { m_pinsBv = 65; });
    DECL_OPTION("-no-pins64", CbCall, [this]() { m_pinsBv = 33; });
    DECL_OPTION("-pins-bv", CbVal, [this, fl](const char* valp) {
        m_pinsBv = std::atoi(valp);
        if (m_pinsBv > 65) fl->v3fatal("--pins-bv maximum is 65: " << valp);
    });
    DECL_OPTION("-pins-sc-uint", CbOnOff, [this](bool flag) {
        m_pinsScUint = flag;
        if (!m_pinsScBigUint) m_pinsBv = 65;
    });
    DECL_OPTION("-pins-sc-biguint", CbOnOff, [this](bool flag) {
        m_pinsScBigUint = flag;
        m_pinsBv = 513;
    });
    DECL_OPTION("-pins-uint8", OnOff, &m_pinsUint8);
    DECL_OPTION("-pipe-filter", Set, &m_pipeFilter);
    DECL_OPTION("-pp-comments", OnOff, &m_ppComments);
    DECL_OPTION("-prefix", Set, &m_prefix);
    DECL_OPTION("-private", CbCall, [this]() { m_public = false; });
    DECL_OPTION("-prof-c", OnOff, &m_profC);
    DECL_OPTION("-prof-cfuncs", CbCall, [this]() { m_profC = m_profCFuncs = true; });
    DECL_OPTION("-profile-cfuncs", CbCall,
                [this]() { m_profC = m_profCFuncs = true; });  // Renamed
    DECL_OPTION("-prof-exec", OnOff, &m_profExec);
    DECL_OPTION("-prof-pgo", OnOff, &m_profPgo);
    DECL_OPTION("-prof-threads", CbOnOff, [this, fl](bool flag) {
        fl->v3warn(DEPRECATED, "Option --prof-threads is deprecated. "
                               "Use --prof-exec and --prof-pgo instead.");
        m_profExec = m_profPgo = flag;
    });
    DECL_OPTION("-protect-ids", OnOff, &m_protectIds);
    DECL_OPTION("-protect-key", Set, &m_protectKey);
    DECL_OPTION("-protect-lib", CbVal, [this](const char* valp) {
        m_libCreate = valp;
        m_protectIds = true;
    });
    DECL_OPTION("-public", OnOff, &m_public);
    DECL_OPTION("-public-flat-rw", CbOnOff, [this](bool flag) {
        m_publicFlatRW = flag;
        v3Global.dpi(true);
    });

    DECL_OPTION("-quiet-exit", OnOff, &m_quietExit);

    DECL_OPTION("-relative-includes", OnOff, &m_relativeIncludes);
    DECL_OPTION("-reloop-limit", CbVal, [this, fl](const char* valp) {
        m_reloopLimit = std::atoi(valp);
        if (m_reloopLimit < 2) { fl->v3error("--reloop-limit must be >= 2: " << valp); }
    });
    DECL_OPTION("-report-unoptflat", OnOff, &m_reportUnoptflat);
    DECL_OPTION("-rr", CbCall, []() {});  // Processed only in bin/verilator shell

    DECL_OPTION("-savable", OnOff, &m_savable);
    DECL_OPTION("-sc", CbCall, [this]() {
        m_outFormatOk = true;
        m_systemC = true;
    });
    DECL_OPTION("-skip-identical", OnOff, &m_skipIdentical);
    DECL_OPTION("-stats", OnOff, &m_stats);
    DECL_OPTION("-stats-vars", CbOnOff, [this](bool flag) {
        m_statsVars = flag;
        m_stats |= flag;
    });
    DECL_OPTION("-structs-unpacked", OnOff, &m_structsPacked);
    DECL_OPTION("-sv", CbCall, [this]() { m_defaultLanguage = V3LangCode::L1800_2017; });

    DECL_OPTION("-threads-coarsen", OnOff, &m_threadsCoarsen).undocumented();  // Debug
    DECL_OPTION("-no-threads", CbCall, [this]() { m_threads = 0; });
    DECL_OPTION("-threads", CbVal, [this, fl](const char* valp) {
        m_threads = std::atoi(valp);
        if (m_threads < 0) fl->v3fatal("--threads must be >= 0: " << valp);
    });
    DECL_OPTION("-threads-dpi", CbVal, [this, fl](const char* valp) {
        if (!strcmp(valp, "all")) {
            m_threadsDpiPure = true;
            m_threadsDpiUnpure = true;
        } else if (!strcmp(valp, "none")) {
            m_threadsDpiPure = false;
            m_threadsDpiUnpure = false;
        } else if (!strcmp(valp, "pure")) {
            m_threadsDpiPure = true;
            m_threadsDpiUnpure = false;
        } else {
            fl->v3fatal("Unknown setting for --threads-dpi: '"
                        << valp << "'\n"
                        << fl->warnMore() << "... Suggest 'all', 'none', or 'pure'");
        }
    });
    DECL_OPTION("-threads-max-mtasks", CbVal, [this, fl](const char* valp) {
        m_threadsMaxMTasks = std::atoi(valp);
        if (m_threadsMaxMTasks < 1) fl->v3fatal("--threads-max-mtasks must be >= 1: " << valp);
    });
    DECL_OPTION("-timescale", CbVal, [this, fl](const char* valp) {
        VTimescale unit;
        VTimescale prec;
        VTimescale::parseSlashed(fl, valp, unit /*ref*/, prec /*ref*/);
        if (!unit.isNone() && timeOverrideUnit().isNone()) m_timeDefaultUnit = unit;
        if (!prec.isNone() && timeOverridePrec().isNone()) m_timeDefaultPrec = prec;
    });
    DECL_OPTION("-timescale-override", CbVal, [this, fl](const char* valp) {
        VTimescale unit;
        VTimescale prec;
        VTimescale::parseSlashed(fl, valp, unit /*ref*/, prec /*ref*/, true);
        if (!unit.isNone()) {
            m_timeDefaultUnit = unit;
            m_timeOverrideUnit = unit;
        }
        if (!prec.isNone()) {
            m_timeDefaultPrec = prec;
            m_timeOverridePrec = prec;
        }
    });
    DECL_OPTION("-top-module", Set, &m_topModule);
    DECL_OPTION("-top", Set, &m_topModule);
    DECL_OPTION("-trace", OnOff, &m_trace);
    DECL_OPTION("-trace-coverage", OnOff, &m_traceCoverage);
    DECL_OPTION("-trace-depth", Set, &m_traceDepth);
    DECL_OPTION("-trace-fst", CbCall, [this]() {
        m_trace = true;
        m_traceFormat = TraceFormat::FST;
        addLdLibs("-lz");
    });
    DECL_OPTION("-trace-fst-thread", CbCall, [this, fl]() {
        m_trace = true;
        m_traceFormat = TraceFormat::FST;
        addLdLibs("-lz");
        fl->v3warn(DEPRECATED, "Option --trace-fst-thread is deprecated. "
                               "Use --trace-fst with --trace-threads > 0.");
        if (m_traceThreads == 0) m_traceThreads = 1;
    });
    DECL_OPTION("-trace-max-array", Set, &m_traceMaxArray);
    DECL_OPTION("-trace-max-width", Set, &m_traceMaxWidth);
    DECL_OPTION("-trace-params", OnOff, &m_traceParams);
    DECL_OPTION("-trace-structs", OnOff, &m_traceStructs);
    DECL_OPTION("-trace-threads", CbVal, [this, fl](const char* valp) {
        m_trace = true;
        m_traceThreads = std::atoi(valp);
        if (m_traceThreads < 1) fl->v3fatal("--trace-threads must be >= 1: " << valp);
    });
    DECL_OPTION("-trace-underscore", OnOff, &m_traceUnderscore);

    DECL_OPTION("-U", CbPartialMatch, &V3PreShell::undef);
    DECL_OPTION("-underline-zero", OnOff, &m_underlineZero);  // Deprecated
    DECL_OPTION("-unroll-count", Set, &m_unrollCount).undocumented();  // Optimization tweak
    DECL_OPTION("-unroll-stmts", Set, &m_unrollStmts).undocumented();  // Optimization tweak
    DECL_OPTION("-unused-regexp", Set, &m_unusedRegexp);

    DECL_OPTION("-V", CbCall, [this]() {
        showVersion(true);
        std::exit(0);
    });
    DECL_OPTION("-v", CbVal, [this, &optdir](const char* valp) {
        V3Options::addLibraryFile(parseFileArg(optdir, valp));
    });
    DECL_OPTION("-verilate", OnOff, &m_verilate);
    DECL_OPTION("-version", CbCall, [this]() {
        showVersion(false);
        std::exit(0);
    });
    DECL_OPTION("-vpi", OnOff, &m_vpi);

    DECL_OPTION("-Wpedantic", OnOff, &m_pedantic);
    DECL_OPTION("-Wall", CbCall, []() {
        FileLine::globalWarnLintOff(false);
        FileLine::globalWarnStyleOff(false);
    });
    DECL_OPTION("-Werror-", CbPartialMatch, [this, fl](const char* optp) {
        const V3ErrorCode code(optp);
        if (code == V3ErrorCode::EC_ERROR) {
            if (!isFuture(optp)) fl->v3fatal("Unknown warning specified: -Werror-" << optp);
        } else {
            V3Error::pretendError(code, true);
        }
    });
    DECL_OPTION("-Wfuture-", CbPartialMatch, [this](const char* optp) {
        // Note it may not be a future option, but one that is currently implemented.
        addFuture(optp);
    });
    DECL_OPTION("-Wno-", CbPartialMatch, [fl, &parser](const char* optp) {
        if (!FileLine::globalWarnOff(optp, true)) {
            const string fullopt = std::string{"-Wno-"} + optp;
            fl->v3fatal("Unknown warning specified: " << fullopt
                                                      << parser.getSuggestion(fullopt.c_str()));
        }
    });
    for (int i = V3ErrorCode::EC_FIRST_WARN; i < V3ErrorCode::_ENUM_MAX; ++i) {
        for (const string prefix : {"-Wno-", "-Wwarn-"})
            parser.addSuggestionCandidate(prefix + V3ErrorCode{i}.ascii());
    }
    DECL_OPTION("-Wno-context", CbCall, [this]() { m_context = false; });
    DECL_OPTION("-Wno-fatal", CbCall, []() { V3Error::warnFatal(false); });
    DECL_OPTION("-Wno-lint", CbCall, []() {
        FileLine::globalWarnLintOff(true);
        FileLine::globalWarnStyleOff(true);
    });
    DECL_OPTION("-Wno-style", CbCall, []() { FileLine::globalWarnStyleOff(true); });
    DECL_OPTION("-Wwarn-", CbPartialMatch, [this, fl, &parser](const char* optp) {
        const V3ErrorCode code{optp};
        if (code == V3ErrorCode::EC_ERROR) {
            if (!isFuture(optp)) {
                const string fullopt = std::string{"-Wwarn-"} + optp;
                fl->v3fatal("Unknown warning specified: "
                            << fullopt << parser.getSuggestion(fullopt.c_str()));
            }
        } else {
            FileLine::globalWarnOff(code, false);
            V3Error::pretendError(code, false);
        }
    });
    DECL_OPTION("-Wwarn-lint", CbCall, []() { FileLine::globalWarnLintOff(false); });
    DECL_OPTION("-Wwarn-style", CbCall, []() { FileLine::globalWarnStyleOff(false); });
    DECL_OPTION("-waiver-output", Set, &m_waiverOutput);

    DECL_OPTION("-x-assign", CbVal, [this, fl](const char* valp) {
        if (!strcmp(valp, "0")) {
            m_xAssign = "0";
        } else if (!strcmp(valp, "1")) {
            m_xAssign = "1";
        } else if (!strcmp(valp, "fast")) {
            m_xAssign = "fast";
        } else if (!strcmp(valp, "unique")) {
            m_xAssign = "unique";
        } else {
            fl->v3fatal("Unknown setting for --x-assign: '"
                        << valp << "'\n"
                        << fl->warnMore() << "... Suggest '0', '1', 'fast', or 'unique'");
        }
    });
    DECL_OPTION("-x-initial", CbVal, [this, fl](const char* valp) {
        if (!strcmp(valp, "0")) {
            m_xInitial = "0";
        } else if (!strcmp(valp, "fast")) {
            m_xInitial = "fast";
        } else if (!strcmp(valp, "unique")) {
            m_xInitial = "unique";
        } else {
            fl->v3fatal("Unknown setting for --x-initial: '"
                        << valp << "'\n"
                        << fl->warnMore() << "... Suggest '0', 'fast', or 'unique'");
        }
    });
    DECL_OPTION("-x-initial-edge", OnOff, &m_xInitialEdge);
    DECL_OPTION("-xml-only", OnOff, &m_xmlOnly);
    DECL_OPTION("-xml-output", CbVal, [this](const char* valp) {
        m_xmlOutput = valp;
        m_xmlOnly = true;
    });

    DECL_OPTION("-y", CbVal, [this, &optdir](const char* valp) {
        addIncDirUser(parseFileArg(optdir, string(valp)));
    });
    parser.finalize();

    for (int i = 0; i < argc;) {
        UINFO(9, " Option: " << argv[i] << endl);
        if (!strcmp(argv[i], "-j") || !strcmp(argv[i], "--j")) {  // Allow gnu -- switches
            ++i;
            m_buildJobs = 0;  // Unlimited parallelism
            if (i < argc && isdigit(argv[i][0])) {
                m_buildJobs = atoi(argv[i]);
                if (m_buildJobs <= 0) {
                    fl->v3error("-j accepts positive integer, but '" << argv[i] << "' is passed");
                }
                ++i;
            }
        } else if (argv[i][0] == '-' || argv[i][0] == '+') {
            const char* argvNoDashp = (argv[i][1] == '-') ? (argv[i] + 2) : (argv[i] + 1);
            if (const int consumed = parser.parse(i, argc, argv)) {
                i += consumed;
            } else if (isFuture0(argvNoDashp)) {
                ++i;
            } else if (isFuture1(argvNoDashp)) {
                i += 2;
            } else {
                fl->v3fatal("Invalid option: " << argv[i] << parser.getSuggestion(argv[i]));
                ++i;  // LCOV_EXCL_LINE
            }
        } else {
            // Filename
            const string filename = parseFileArg(optdir, argv[i]);
            if (suffixed(filename, ".cpp")  //
                || suffixed(filename, ".cxx")  //
                || suffixed(filename, ".cc")  //
                || suffixed(filename, ".c")  //
                || suffixed(filename, ".sp")) {
                V3Options::addCppFile(filename);
            } else if (suffixed(filename, ".a")  //
                       || suffixed(filename, ".o")  //
                       || suffixed(filename, ".so")) {
                V3Options::addLdLibs(filename);
            } else {
                V3Options::addVFile(filename);
            }
            ++i;
        }
    }
}

//======================================================================

void V3Options::parseOptsFile(FileLine* fl, const string& filename, bool rel) {
    // Read the specified -f filename and process as arguments
    UINFO(1, "Reading Options File " << filename << endl);

    const std::unique_ptr<std::ifstream> ifp{V3File::new_ifstream(filename)};
    if (ifp->fail()) {
        fl->v3error("Cannot open -f command file: " + filename);
        return;
    }

    string whole_file;
    bool inCmt = false;
    while (!ifp->eof()) {
        const string line = V3Os::getline(*ifp);
        // Strip simple comments
        string oline;
        // cppcheck-suppress StlMissingComparison
        char lastch = ' ';
        bool space_begin = true;  // At beginning or leading spaces only
        for (string::const_iterator pos = line.begin(); pos != line.end(); lastch = *pos++) {
            if (inCmt) {
                if (*pos == '*' && *(pos + 1) == '/') {
                    inCmt = false;
                    ++pos;
                }
            } else if (*pos == '/' && *(pos + 1) == '/'
                       && (pos == line.begin() || isspace(lastch))) {  // But allow /file//path
                break;  // Ignore to EOL
            } else if (*pos == '#' && space_begin) {  // Only # at [spaced] begin of line
                break;  // Ignore to EOL
            } else if (*pos == '/' && *(pos + 1) == '*') {
                inCmt = true;
                space_begin = false;
                // cppcheck-suppress StlMissingComparison
                ++pos;
            } else {
                if (!isspace(*pos)) space_begin = false;
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
    enum state : uint8_t {
        ST_IN_OPTION,
        ST_ESCAPED_CHAR,
        ST_IN_QUOTED_STR,
        ST_IN_DOUBLE_QUOTED_STR
    };

    state st = ST_IN_OPTION;
    state last_st = ST_IN_OPTION;
    string arg;
    for (string::size_type pos = 0; pos < whole_file.length(); ++pos) {
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
                arg += curr_char;
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
    const string optdir = (rel ? V3Os::filenameDir(filename) : ".");

    // Convert to argv style arg list and parse them
    std::vector<char*> argv;
    argv.reserve(args.size() + 1);
    for (const string& i : args) argv.push_back(const_cast<char*>(i.c_str()));
    argv.push_back(nullptr);  // argv is nullptr-terminated
    parseOptsList(fl, optdir, static_cast<int>(argv.size() - 1), argv.data());
}

//======================================================================

string V3Options::parseFileArg(const string& optdir, const string& relfilename) {
    string filename = V3Os::filenameSubstitute(relfilename);
    if (optdir != "." && V3Os::filenameIsRel(filename)) filename = optdir + "/" + filename;
    return filename;
}

//======================================================================

void V3Options::showVersion(bool verbose) {
    cout << version();
    cout << endl;
    if (!verbose) return;

    cout << endl;
    cout << "Copyright 2003-2022 by Wilson Snyder.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout << endl;
    cout << "See https://verilator.org for documentation\n";

    cout << endl;
    cout << "Summary of configuration:\n";
    cout << "  Compiled in defaults if not in environment:\n";
    cout << "    SYSTEMC            = " << DEFENV_SYSTEMC << endl;
    cout << "    SYSTEMC_ARCH       = " << DEFENV_SYSTEMC_ARCH << endl;
    cout << "    SYSTEMC_INCLUDE    = " << DEFENV_SYSTEMC_INCLUDE << endl;
    cout << "    SYSTEMC_LIBDIR     = " << DEFENV_SYSTEMC_LIBDIR << endl;
    cout << "    VERILATOR_ROOT     = " << DEFENV_VERILATOR_ROOT << endl;
    cout << "    SystemC system-wide = " << cvtToStr(systemCSystemWide()) << endl;

    cout << endl;
    cout << "Environment:\n";
    cout << "    MAKE               = " << V3Os::getenvStr("MAKE", "") << endl;
    cout << "    PERL               = " << V3Os::getenvStr("PERL", "") << endl;
    cout << "    SYSTEMC            = " << V3Os::getenvStr("SYSTEMC", "") << endl;
    cout << "    SYSTEMC_ARCH       = " << V3Os::getenvStr("SYSTEMC_ARCH", "") << endl;
    cout << "    SYSTEMC_INCLUDE    = " << V3Os::getenvStr("SYSTEMC_INCLUDE", "") << endl;
    cout << "    SYSTEMC_LIBDIR     = " << V3Os::getenvStr("SYSTEMC_LIBDIR", "") << endl;
    cout << "    VERILATOR_ROOT     = " << V3Os::getenvStr("VERILATOR_ROOT", "") << endl;
    // wrapper uses this:
    cout << "    VERILATOR_BIN      = " << V3Os::getenvStr("VERILATOR_BIN", "") << endl;

    cout << endl;
    cout << "Features (based on environment or compiled-in support):\n";
    cout << "    SystemC found      = " << cvtToStr(systemCFound()) << endl;
}

//======================================================================

V3Options::V3Options() {
    m_impp = new V3OptionsImp;

    m_traceFormat = TraceFormat::VCD;

    m_makeDir = "obj_dir";
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

V3Options::~V3Options() { VL_DO_CLEAR(delete m_impp, m_impp = nullptr); }

void V3Options::setDebugMode(int level) {
    V3Error::debugDefault(level);
    if (!m_dumpTree) m_dumpTree = 3;  // Don't override if already set.
    m_stats = true;
    m_debugCheck = true;
    cout << "Starting " << version() << endl;
}

void V3Options::setDebugSrcLevel(const string& srcfile, int level) {
    const auto iter = m_debugSrcs.find(srcfile);
    if (iter != m_debugSrcs.end()) {
        iter->second = level;
    } else {
        m_debugSrcs.emplace(srcfile, level);
    }
}

int V3Options::debugSrcLevel(const string& srcfile_path, int default_level) {
    // For simplicity, calling functions can just use __FILE__ for srcfile.
    // That means though we need to cleanup the filename from ../Foo.cpp -> Foo
    const string srcfile = V3Os::filenameNonDirExt(srcfile_path);
    const auto iter = m_debugSrcs.find(srcfile);
    if (iter != m_debugSrcs.end()) {
        return iter->second;
    } else {
        return default_level;
    }
}

void V3Options::setDumpTreeLevel(const string& srcfile, int level) {
    const auto iter = m_dumpTrees.find(srcfile);
    if (iter != m_dumpTrees.end()) {
        iter->second = level;
    } else {
        m_dumpTrees.emplace(srcfile, level);
    }
}

int V3Options::dumpTreeLevel(const string& srcfile_path) {
    // For simplicity, calling functions can just use __FILE__ for srcfile.
    // That means though we need to cleanup the filename from ../Foo.cpp -> Foo
    const string srcfile = V3Os::filenameNonDirExt(srcfile_path);
    const auto iter = m_dumpTrees.find(srcfile);
    if (iter != m_dumpTrees.end()) {
        return iter->second;
    } else {
        return m_dumpTree;
    }
}

void V3Options::optimize(int level) {
    // Set all optimizations to on/off
    const bool flag = level > 0;
    m_fAcycSimp = flag;
    m_fAssemble = flag;
    m_fCase = flag;
    m_fCombine = flag;
    m_fConst = flag;
    m_fConstBitOpTree = flag;
    m_fDedupe = flag;
    m_fExpand = flag;
    m_fGate = flag;
    m_fInline = flag;
    m_fLife = flag;
    m_fLifePost = flag;
    m_fLocalize = flag;
    m_fMergeCond = flag;
    m_fReloop = flag;
    m_fReorder = flag;
    m_fSplit = flag;
    m_fSubst = flag;
    m_fSubstConst = flag;
    m_fTable = flag;
    // And set specific optimization levels
    if (level >= 3) {
        m_inlineMult = -1;  // Maximum inlining
    }
}
