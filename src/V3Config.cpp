// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configuration Files
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2010-2021 by Wilson Snyder. This program is free software; you
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
#include "V3Config.h"

#include <map>
#include <set>
#include <string>

//######################################################################
// Resolve wildcards in files, modules, ftasks or variables

// Template for a class that serves as a map for entities that can be specified
// as wildcards and are accessed by a resolved name. It rebuilds a name lookup
// cache of resolved entities. Entities stored in this container need an update
// function that takes a reference of this type to join multiple entities into one.
template <typename T> class V3ConfigWildcardResolver {
    using Map = std::map<const std::string, T>;

    Map m_mapWildcard;  // Wildcard strings to entities
    Map m_mapResolved;  // Resolved strings to converged entities
public:
    V3ConfigWildcardResolver() = default;
    ~V3ConfigWildcardResolver() = default;

    /// Update into maps from other
    void update(const V3ConfigWildcardResolver& other) {
        typename Map::const_iterator it;
        for (it = other.m_mapResolved.begin(); it != other.m_mapResolved.end(); ++it) {
            m_mapResolved[it->first].update(it->second);
        }
        for (it = other.m_mapWildcard.begin(); it != other.m_mapWildcard.end(); ++it) {
            m_mapWildcard[it->first].update(it->second);
        }
    }

    // Access and create a (wildcard) entity
    T& at(const string& name) {
        // Don't store into wildcards if the name is not a wildcard string
        return m_mapWildcard[name];
    }
    // Access an entity and resolve wildcards that match it
    T* resolve(const string& name) {
        // Lookup if it was resolved before, typically not
        auto it = m_mapResolved.find(name);
        if (VL_UNLIKELY(it != m_mapResolved.end())) return &it->second;

        T* newp = nullptr;
        // Cannot be resolved, create if matched

        // Update this entity with all matches in the wildcards
        for (it = m_mapWildcard.begin(); it != m_mapWildcard.end(); ++it) {
            if (VString::wildmatch(name, it->first)) {
                if (!newp) {
                    newp = &m_mapResolved[name];  // Emplace and get pointer
                }
                newp->update(it->second);
            }
        }
        return newp;
    }
    // Flush on update
    void flush() { m_mapResolved.clear(); }
};

// Only public_flat_rw has the sensitity tree
class V3ConfigVarAttr final {
public:
    AstAttrType m_type;  // Type of attribute
    AstSenTree* m_sentreep;  // Sensitivity tree for public_flat_rw
    V3ConfigVarAttr(AstAttrType type, AstSenTree* sentreep)
        : m_type{type}
        , m_sentreep{sentreep} {}
};

// Overload vector with the required update function and to apply all entries
class V3ConfigVar final : public std::vector<V3ConfigVarAttr> {
public:
    // Update from other by copying all attributes
    void update(const V3ConfigVar& node) {
        reserve(size() + node.size());
        insert(end(), node.begin(), node.end());
    }
    // Apply all attributes to the variable
    void apply(AstVar* varp) {
        for (const_iterator it = begin(); it != end(); ++it) {
            AstNode* newp = new AstAttrOf(varp->fileline(), it->m_type);
            varp->addAttrsp(newp);
            if (it->m_type == AstAttrType::VAR_PUBLIC_FLAT_RW && it->m_sentreep) {
                newp->addNext(new AstAlwaysPublic(varp->fileline(), it->m_sentreep, nullptr));
            }
        }
    }
};

using V3ConfigVarResolver = V3ConfigWildcardResolver<V3ConfigVar>;

//######################################################################
// Function or task: Have variables and properties

class V3ConfigFTask final {
    V3ConfigVarResolver m_vars;  // Variables in function/task
    bool m_isolate = false;  // Isolate function return
    bool m_noinline = false;  // Don't inline function/task
    bool m_public = false;  // Public function/task

public:
    V3ConfigFTask() = default;
    void update(const V3ConfigFTask& f) {
        // Don't overwrite true with false
        if (f.m_isolate) m_isolate = true;
        if (f.m_noinline) m_noinline = true;
        if (f.m_public) m_public = true;
        m_vars.update(f.m_vars);
    }

    V3ConfigVarResolver& vars() { return m_vars; }

    void setIsolate(bool set) { m_isolate = set; }
    void setNoInline(bool set) { m_noinline = set; }
    void setPublic(bool set) { m_public = set; }

    void apply(AstNodeFTask* ftaskp) const {
        if (m_noinline)
            ftaskp->addStmtsp(new AstPragma(ftaskp->fileline(), AstPragmaType::NO_INLINE_TASK));
        if (m_public)
            ftaskp->addStmtsp(new AstPragma(ftaskp->fileline(), AstPragmaType::PUBLIC_TASK));
        // Only functions can have isolate (return value)
        if (VN_IS(ftaskp, Func)) ftaskp->attrIsolateAssign(m_isolate);
    }
};

using V3ConfigFTaskResolver = V3ConfigWildcardResolver<V3ConfigFTask>;

//######################################################################
// Modules have tasks, variables, named blocks and properties

class V3ConfigModule final {
    V3ConfigFTaskResolver m_tasks;  // Functions/tasks in module
    V3ConfigVarResolver m_vars;  // Variables in module
    std::unordered_set<std::string> m_coverageOffBlocks;  // List of block names for coverage_off
    std::set<AstPragmaType> m_modPragmas;  // List of Pragmas for modules
    bool m_inline = false;  // Whether to force the inline
    bool m_inlineValue = false;  // The inline value (on/off)

public:
    V3ConfigModule() = default;

    void update(const V3ConfigModule& m) {
        m_tasks.update(m.m_tasks);
        m_vars.update(m.m_vars);
        for (const string& i : m.m_coverageOffBlocks) m_coverageOffBlocks.insert(i);
        if (!m_inline) {
            m_inline = m.m_inline;
            m_inlineValue = m.m_inlineValue;
        }
        for (auto it = m.m_modPragmas.cbegin(); it != m.m_modPragmas.cend(); ++it) {
            m_modPragmas.insert(*it);
        }
    }

    V3ConfigFTaskResolver& ftasks() { return m_tasks; }
    V3ConfigVarResolver& vars() { return m_vars; }

    void addCoverageBlockOff(const string& name) { m_coverageOffBlocks.insert(name); }
    void setInline(bool set) {
        m_inline = true;
        m_inlineValue = set;
    }
    void addModulePragma(AstPragmaType pragma) { m_modPragmas.insert(pragma); }

    void apply(AstNodeModule* modp) {
        if (m_inline) {
            AstPragmaType type
                = m_inlineValue ? AstPragmaType::INLINE_MODULE : AstPragmaType::NO_INLINE_MODULE;
            AstNode* nodep = new AstPragma(modp->fileline(), type);
            modp->addStmtp(nodep);
        }
        for (auto it = m_modPragmas.cbegin(); it != m_modPragmas.cend(); ++it) {
            AstNode* nodep = new AstPragma(modp->fileline(), *it);
            modp->addStmtp(nodep);
        }
    }

    void applyBlock(AstNodeBlock* nodep) {
        const AstPragmaType pragma = AstPragmaType::COVERAGE_BLOCK_OFF;
        if (!nodep->unnamed()) {
            for (const string& i : m_coverageOffBlocks) {
                if (VString::wildmatch(nodep->name(), i)) {
                    nodep->addStmtsp(new AstPragma(nodep->fileline(), pragma));
                }
            }
        }
    }
};

using V3ConfigModuleResolver = V3ConfigWildcardResolver<V3ConfigModule>;

//######################################################################
// Files have:
//  - Line ignores (lint/coverage/tracing on/off)
//  - Line attributes: Attributes attached to lines

// lint/coverage/tracing on/off
class V3ConfigIgnoresLine final {
public:
    int m_lineno;  // Line number to make change at
    V3ErrorCode m_code;  // Error code
    bool m_on;  // True to enable message
    V3ConfigIgnoresLine(V3ErrorCode code, int lineno, bool on)
        : m_lineno{lineno}
        , m_code{code}
        , m_on{on} {}
    ~V3ConfigIgnoresLine() = default;
    bool operator<(const V3ConfigIgnoresLine& rh) const {
        if (m_lineno < rh.m_lineno) return true;
        if (m_lineno > rh.m_lineno) return false;
        if (m_code < rh.m_code) return true;
        if (m_code > rh.m_code) return false;
        // Always turn "on" before "off" so that overlapping lines will end
        // up finally with the error "off"
        return (m_on > rh.m_on);
    }
};
std::ostream& operator<<(std::ostream& os, const V3ConfigIgnoresLine& rhs) {
    return os << rhs.m_lineno << ", " << rhs.m_code << ", " << rhs.m_on;
}

// Some attributes are attached to entities of the occur on a fileline
// and multiple attributes can be attached to a line
using V3ConfigLineAttribute = std::bitset<AstPragmaType::ENUM_SIZE>;

// File entity
class V3ConfigFile final {
    using LineAttrMap = std::map<int, V3ConfigLineAttribute>;  // Map line->bitset of attributes
    using IgnLines = std::multiset<V3ConfigIgnoresLine>;  // list of {line,code,on}
    using WaiverSetting = std::pair<V3ErrorCode, std::string>;  // Waive code if string matches
    using Waivers = std::vector<WaiverSetting>;  // List of {code,wildcard string}

    LineAttrMap m_lineAttrs;  // Atributes to line mapping
    IgnLines m_ignLines;  // Ignore line settings
    Waivers m_waivers;  // Waive messages

    struct {
        int lineno;  // Last line number
        IgnLines::const_iterator it;  // Point with next linenumber > current line number
    } m_lastIgnore;  // Last ignore line run

    // Match a given line and attribute to the map, line 0 is any
    bool lineMatch(int lineno, AstPragmaType type) {
        if (m_lineAttrs.find(0) != m_lineAttrs.end() && m_lineAttrs[0][type]) return true;
        if (m_lineAttrs.find(lineno) == m_lineAttrs.end()) return false;
        return m_lineAttrs[lineno][type];
    }

public:
    V3ConfigFile() {
        m_lastIgnore.lineno = -1;
        m_lastIgnore.it = m_ignLines.begin();
    }
    void update(const V3ConfigFile& file) {
        // Copy in all Attributes
        for (const auto& itr : file.m_lineAttrs) { m_lineAttrs[itr.first] |= itr.second; }
        // Copy in all ignores
        for (const auto& ignLine : file.m_ignLines) m_ignLines.insert(ignLine);
        // Update the iterator after the list has changed
        m_lastIgnore.it = m_ignLines.begin();
        m_waivers.reserve(m_waivers.size() + file.m_waivers.size());
        m_waivers.insert(m_waivers.end(), file.m_waivers.begin(), file.m_waivers.end());
    }
    void addLineAttribute(int lineno, AstPragmaType attr) { m_lineAttrs[lineno].set(attr); }
    void addIgnore(V3ErrorCode code, int lineno, bool on) {
        m_ignLines.insert(V3ConfigIgnoresLine(code, lineno, on));
        m_lastIgnore.it = m_ignLines.begin();
    }
    void addWaiver(V3ErrorCode code, const string& match) {
        m_waivers.push_back(std::make_pair(code, match));
    }

    void applyBlock(AstNodeBlock* nodep) {
        // Apply to block at this line
        const AstPragmaType pragma = AstPragmaType::COVERAGE_BLOCK_OFF;
        if (lineMatch(nodep->fileline()->lineno(), pragma)) {
            nodep->addStmtsp(new AstPragma(nodep->fileline(), pragma));
        }
    }
    void applyCase(AstCase* nodep) {
        // Apply to this case at this line
        const int lineno = nodep->fileline()->lineno();
        if (lineMatch(lineno, AstPragmaType::FULL_CASE)) nodep->fullPragma(true);
        if (lineMatch(lineno, AstPragmaType::PARALLEL_CASE)) nodep->parallelPragma(true);
    }
    inline void applyIgnores(FileLine* filelinep) {
        // HOT routine, called each parsed token line of this filename
        if (m_lastIgnore.lineno != filelinep->lineno()) {
            // UINFO(9, "   ApplyIgnores for " << filelinep->ascii() << endl);
            // Process all on/offs for lines up to and including the current line
            const int curlineno = filelinep->lastLineno();
            for (; m_lastIgnore.it != m_ignLines.end(); ++m_lastIgnore.it) {
                if (m_lastIgnore.it->m_lineno > curlineno) break;
                // UINFO(9, "     Hit " << *m_lastIt << endl);
                filelinep->warnOn(m_lastIgnore.it->m_code, m_lastIgnore.it->m_on);
            }
            if (false && debug() >= 9) {
                for (IgnLines::const_iterator it = m_lastIgnore.it; it != m_ignLines.end(); ++it) {
                    UINFO(9, "     NXT " << *it << endl);
                }
            }
            m_lastIgnore.lineno = filelinep->lastLineno();
        }
    }
    bool waive(V3ErrorCode code, const string& match) {
        for (const auto& itr : m_waivers) {
            if (((itr.first == code) || (itr.first == V3ErrorCode::I_LINT))
                && VString::wildmatch(match, itr.second)) {
                return true;
            }
        }
        return false;
    }
};

using V3ConfigFileResolver = V3ConfigWildcardResolver<V3ConfigFile>;

//######################################################################
// Resolve modules and files in the design

class V3ConfigResolver final {
    V3ConfigModuleResolver m_modules;  // Access to module names (with wildcards)
    V3ConfigFileResolver m_files;  // Access to file names (with wildcards)

    static V3ConfigResolver s_singleton;  // Singleton (not via local static, as that's slow)
    V3ConfigResolver() = default;
    ~V3ConfigResolver() = default;

public:
    static V3ConfigResolver& s() { return s_singleton; }

    V3ConfigModuleResolver& modules() { return m_modules; }
    V3ConfigFileResolver& files() { return m_files; }
};

V3ConfigResolver V3ConfigResolver::s_singleton;

//######################################################################
// V3Config

void V3Config::addCaseFull(const string& filename, int lineno) {
    V3ConfigFile& file = V3ConfigResolver::s().files().at(filename);
    file.addLineAttribute(lineno, AstPragmaType::FULL_CASE);
}

void V3Config::addCaseParallel(const string& filename, int lineno) {
    V3ConfigFile& file = V3ConfigResolver::s().files().at(filename);
    file.addLineAttribute(lineno, AstPragmaType::PARALLEL_CASE);
}

void V3Config::addCoverageBlockOff(const string& filename, int lineno) {
    V3ConfigFile& file = V3ConfigResolver::s().files().at(filename);
    file.addLineAttribute(lineno, AstPragmaType::COVERAGE_BLOCK_OFF);
}

void V3Config::addCoverageBlockOff(const string& module, const string& blockname) {
    V3ConfigResolver::s().modules().at(module).addCoverageBlockOff(blockname);
}

void V3Config::addIgnore(V3ErrorCode code, bool on, const string& filename, int min, int max) {
    if (filename == "*") {
        FileLine::globalWarnOff(code, !on);
    } else {
        V3ConfigResolver::s().files().at(filename).addIgnore(code, min, on);
        if (max) V3ConfigResolver::s().files().at(filename).addIgnore(code, max, !on);
        V3ConfigResolver::s().files().flush();
    }
}

void V3Config::addModulePragma(const string& module, AstPragmaType pragma) {
    V3ConfigResolver::s().modules().at(module).addModulePragma(pragma);
}

void V3Config::addInline(FileLine* fl, const string& module, const string& ftask, bool on) {
    if (ftask.empty()) {
        V3ConfigResolver::s().modules().at(module).setInline(on);
    } else {
        if (!on) {
            fl->v3error("no_inline not supported for tasks");
        } else {
            V3ConfigResolver::s().modules().at(module).ftasks().at(ftask).setNoInline(on);
        }
    }
}

void V3Config::addVarAttr(FileLine* fl, const string& module, const string& ftask,
                          const string& var, AstAttrType attr, AstSenTree* sensep) {
    // Semantics: sensep only if public_flat_rw
    if ((attr != AstAttrType::VAR_PUBLIC_FLAT_RW) && sensep) {
        sensep->v3error("sensitivity not expected for attribute");
        return;
    }
    // Semantics: Most of the attributes operate on signals
    if (var.empty()) {
        if (attr == AstAttrType::VAR_ISOLATE_ASSIGNMENTS) {
            if (ftask.empty()) {
                fl->v3error("isolate_assignments only applies to signals or functions/tasks");
            } else {
                V3ConfigResolver::s().modules().at(module).ftasks().at(ftask).setIsolate(true);
            }
        } else if (attr == AstAttrType::VAR_PUBLIC) {
            if (ftask.empty()) {
                // public module, this is the only exception from var here
                V3ConfigResolver::s().modules().at(module).addModulePragma(
                    AstPragmaType::PUBLIC_MODULE);
            } else {
                V3ConfigResolver::s().modules().at(module).ftasks().at(ftask).setPublic(true);
            }
        } else {
            fl->v3error("missing -signal");
        }
    } else {
        V3ConfigModule& mod = V3ConfigResolver::s().modules().at(module);
        if (ftask.empty()) {
            mod.vars().at(var).push_back(V3ConfigVarAttr(attr, sensep));
        } else {
            mod.ftasks().at(ftask).vars().at(var).push_back(V3ConfigVarAttr(attr, sensep));
        }
    }
}

void V3Config::addWaiver(V3ErrorCode code, const string& filename, const string& message) {
    V3ConfigResolver::s().files().at(filename).addWaiver(code, message);
}

void V3Config::applyCase(AstCase* nodep) {
    const string& filename = nodep->fileline()->filename();
    V3ConfigFile* filep = V3ConfigResolver::s().files().resolve(filename);
    if (filep) filep->applyCase(nodep);
}

void V3Config::applyCoverageBlock(AstNodeModule* modulep, AstBegin* nodep) {
    const string& filename = nodep->fileline()->filename();
    V3ConfigFile* filep = V3ConfigResolver::s().files().resolve(filename);
    if (filep) filep->applyBlock(nodep);
    const string& modname = modulep->name();
    V3ConfigModule* modp = V3ConfigResolver::s().modules().resolve(modname);
    if (modp) modp->applyBlock(nodep);
}

void V3Config::applyIgnores(FileLine* filelinep) {
    const string& filename = filelinep->filename();
    V3ConfigFile* filep = V3ConfigResolver::s().files().resolve(filename);
    if (filep) filep->applyIgnores(filelinep);
}

void V3Config::applyModule(AstNodeModule* modulep) {
    const string& modname = modulep->name();
    V3ConfigModule* modp = V3ConfigResolver::s().modules().resolve(modname);
    if (modp) modp->apply(modulep);
}

void V3Config::applyFTask(AstNodeModule* modulep, AstNodeFTask* ftaskp) {
    const string& modname = modulep->name();
    V3ConfigModule* modp = V3ConfigResolver::s().modules().resolve(modname);
    if (!modp) return;
    V3ConfigFTask* ftp = modp->ftasks().resolve(ftaskp->name());
    if (ftp) ftp->apply(ftaskp);
}

void V3Config::applyVarAttr(AstNodeModule* modulep, AstNodeFTask* ftaskp, AstVar* varp) {
    V3ConfigVar* vp;
    V3ConfigModule* modp = V3ConfigResolver::s().modules().resolve(modulep->name());
    if (!modp) return;
    if (ftaskp) {
        V3ConfigFTask* ftp = modp->ftasks().resolve(ftaskp->name());
        if (!ftp) return;
        vp = ftp->vars().resolve(varp->name());
    } else {
        vp = modp->vars().resolve(varp->name());
    }
    if (vp) vp->apply(varp);
}

bool V3Config::waive(FileLine* filelinep, V3ErrorCode code, const string& message) {
    V3ConfigFile* filep = V3ConfigResolver::s().files().resolve(filelinep->filename());
    if (!filep) return false;
    return filep->waive(code, message);
}
