// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// LinkDot TRANSFORMATIONS:
//      Top-down traversal in LinkDotFindVisitor
//          Cells:
//              Make graph of cell hierarchy
//          Var/Funcs's:
//              Collect all names into symtable under appropriate cell
//      Top-down traversal in LinkDotScopeVisitor
//          Find VarScope versions of signals (well past original link)
//      Top-down traversal in LinkDotParamVisitor
//          Create implicit signals
//      Top-down traversal in LinkDotResolveVisitor
//          VarXRef/Func's:
//              Find appropriate named cell and link to var they reference
//*************************************************************************
// Interfaces:
//      CELL (.port (ifref)
//                     ^--- cell                 -> IfaceDTypeRef(iface)
//                     ^--- cell.modport         -> IfaceDTypeRef(iface,modport)
//                     ^--- varref(input_ifref)  -> IfaceDTypeRef(iface)
//                     ^--- varref(input_ifref).modport -> IfaceDTypeRef(iface,modport)
//      FindVisitor:
//          #1: Insert interface Vars
//          #2: Insert ModPort names
//        IfaceVisitor:
//          #3: Update ModPortVarRef to point at interface vars (after #1)
//          #4: Create ModPortVarRef symbol table entries
//        FindVisitor-insertIfaceRefs()
//          #5: Resolve IfaceRefDtype modport names (after #2)
//          #7: Record sym of IfaceRefDType and aliased interface and/or modport (after #4,#5)
//      insertAllScopeAliases():
//          #8: Insert modport's symbols under IfaceRefDType (after #7)
//      ResolveVisitor:
//          #9: Resolve general variables, which may point into the interface or modport (after #8)
//      LinkResolve:
//          #10: Unlink modports, not needed later except for XML/Lint
//*************************************************************************
// TOP
//      {name-of-top-modulename}
//      a          (VSymEnt->AstCell)
//        {name-of-cell}
//        {name-of-cell-module}
//        aa         (VSymEnt->AstCell)
//          var        (AstVar) -- no sub symbol table needed
//          beg        (VSymEnt->AstBegin) -- can see "upper" a's symbol table
//      a__DOT__aa (VSymEnt->AstCellInline) -- points to a.aa's symbol table
//      b          (VSymEnt->AstCell)
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkDot.h"

#include "V3Graph.h"
#include "V3MemberMap.h"
#include "V3String.h"
#include "V3SymTable.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Matcher classes (for suggestion matching)

class LinkNodeMatcherClass final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override { return VN_IS(nodep, Class); }
};
class LinkNodeMatcherFTask final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override { return VN_IS(nodep, NodeFTask); }
};
class LinkNodeMatcherModport final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override { return VN_IS(nodep, Modport); }
};
class LinkNodeMatcherVar final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override {
        return VN_IS(nodep, Var) || VN_IS(nodep, LambdaArgRef);
    }
};
class LinkNodeMatcherVarIO final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override {
        const AstVar* const varp = VN_CAST(nodep, Var);
        if (!varp) return false;
        return varp->isIO();
    }
};
class LinkNodeMatcherVarParam final : public VNodeMatcher {
public:
    bool nodeMatch(const AstNode* nodep) const override {
        const AstVar* const varp = VN_CAST(nodep, Var);
        if (!varp) return false;
        return varp->isParam();
    }
};

//######################################################################
// LinkDot state, as a visitor of each AstNode

class LinkDotState final {
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1p()         // VSymEnt*.      Last symbol created for this node
    //  AstNodeModule::user2()          // bool.          Currently processing for recursion check
    //  ...  Note maybe more than one, as can be multiple hierarchy places
    //  AstVarScope::user2p()           // AstVarScope*.  Base alias for AstInline of this signal
    //  AstVar::user2p()                // AstFTask*.     If a function variable, the task
    //                                                    that links to the variable
    //  AstVar::user4()                 // bool.          True if port set for this variable
    //  AstNodeBlock::user4()           // bool.          Did name processing
    //  AstNodeModule::user4()          // bool.          Live module
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser4InUse m_inuser4;

public:
    // ENUMS
    // In order of priority, compute first ... compute last
    enum SAMNum : uint8_t { SAMN_MODPORT, SAMN_IFTOP, SAMN__MAX };  // Values for m_scopeAliasMap

private:
    // TYPES
    using ScopeAliasMap = std::unordered_map<VSymEnt*, VSymEnt*>;
    using IfaceModSyms = std::vector<std::pair<AstIface*, VSymEnt*>>;

    static LinkDotState* s_errorThisp;  // Last self, for error reporting only

    // MEMBERS
    VSymGraph m_syms;  // Symbol table
    VSymEnt* m_dunitEntp = nullptr;  // $unit entry
    std::multimap<std::string, VSymEnt*>
        m_nameScopeSymMap;  // Map of scope referenced by non-pretty textual name
    std::set<std::pair<AstNodeModule*, std::string>>
        m_implicitNameSet;  // For [module][signalname] if we can implicitly create it
    std::array<ScopeAliasMap, SAMN__MAX> m_scopeAliasMap;  // Map of <lhs,rhs> aliases
    std::vector<VSymEnt*> m_ifaceVarSyms;  // List of AstIfaceRefDType's to be imported
    IfaceModSyms m_ifaceModSyms;  // List of AstIface+Symbols to be processed
    const VLinkDotStep m_step;  // Operational step

public:
    // METHODS

    void dumpSelf(const string& nameComment = "linkdot", bool force = false) {
        if (dumpLevel() >= 6 || force) {
            const string filename = v3Global.debugFilename(nameComment) + ".txt";
            const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
            if (logp->fail()) v3fatal("Can't write " << filename);
            std::ostream& os = *logp;
            m_syms.dumpSelf(os);
            bool first = true;
            for (int samn = 0; samn < SAMN__MAX; ++samn) {
                if (!m_scopeAliasMap[samn].empty()) {
                    if (first) os << "\nScopeAliasMap:\n";
                    first = false;
                    for (ScopeAliasMap::iterator it = m_scopeAliasMap[samn].begin();
                         it != m_scopeAliasMap[samn].end(); ++it) {
                        // left side is what we will import into
                        os << "\t" << samn << "\t" << it->first << " ("
                           << it->first->nodep()->typeName() << ") <- " << it->second << " "
                           << it->second->nodep() << '\n';
                    }
                }
            }
        }
    }
    static void preErrorDumpHandler() {
        if (s_errorThisp) s_errorThisp->preErrorDump();
    }
    void preErrorDump() {
        static bool diddump = false;
        if (!diddump && dumpTreeLevel()) {
            diddump = true;
            dumpSelf("linkdot-preerr", true);
            v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("linkdot-preerr.tree"));
        }
    }

    // CONSTRUCTORS
    LinkDotState(AstNetlist* rootp, VLinkDotStep step)
        : m_syms{rootp}
        , m_step(step) {
        UINFO(4, __FUNCTION__ << ": " << endl);
        s_errorThisp = this;
        V3Error::errorExitCb(preErrorDumpHandler);  // If get error, dump self
    }
    ~LinkDotState() {
        V3Error::errorExitCb(nullptr);
        s_errorThisp = nullptr;
    }

    // ACCESSORS
    VSymGraph* symsp() { return &m_syms; }
    int stepNumber() const { return int(m_step); }
    bool forPrimary() const { return m_step == LDS_PRIMARY; }
    bool forParamed() const { return m_step == LDS_PARAMED; }
    bool forPrearray() const { return m_step == LDS_PARAMED || m_step == LDS_PRIMARY; }
    bool forScopeCreation() const { return m_step == LDS_SCOPED; }

    // METHODS
    static string nodeTextType(AstNode* nodep) {
        if (const AstVar* const varp = VN_CAST(nodep, Var)) {
            if (varp->isIO() || varp->isIfaceRef()) {
                return "port";
            } else if (varp->isGParam()) {
                return "parameter";
            } else if (varp->varType() == VVarType::LPARAM) {
                return "local parameter";
            } else {
                return "variable";
            }
        } else if (const AstParamTypeDType* const dtypep = VN_CAST(nodep, ParamTypeDType)) {
            if (dtypep->isGParam()) {
                return "type parameter";
            } else {
                return "local type parameter";
            }
        } else if (VN_IS(nodep, Cell)) {
            return "instance";
        } else if (VN_IS(nodep, Constraint)) {
            return "constraint";
        } else if (VN_IS(nodep, Task)) {
            return "task";
        } else if (VN_IS(nodep, Func)) {
            return "function";
        } else if (VN_IS(nodep, Begin)) {
            return "block";
        } else if (VN_IS(nodep, Iface)) {
            return "interface";
        } else {
            return nodep->prettyTypeName();
        }
    }

    VSymEnt* rootEntp() const { return m_syms.rootp(); }
    VSymEnt* dunitEntp() const { return m_dunitEntp; }
    void checkDuplicate(VSymEnt* lookupSymp, AstNode* nodep, const string& name) {
        // Lookup the given name under current symbol table
        // Insert if not found
        // Report error if there's a duplicate
        //
        // Note we only check for conflicts at the same level; it's ok if one block hides another
        // We also wouldn't want to not insert it even though it's lower down
        const VSymEnt* const foundp = lookupSymp->findIdFlat(name);
        AstNode* const fnodep = foundp ? foundp->nodep() : nullptr;
        if (!fnodep) {
            // Not found, will add in a moment.
        } else if (nodep == fnodep) {  // Already inserted.
            // Good.
        } else if (foundp->imported()) {  // From package
            // We don't throw VARHIDDEN as if the import is later the symbol
            // table's import wouldn't warn
        } else if (VN_IS(nodep, Begin) && VN_IS(fnodep, Begin)
                   && VN_AS(nodep, Begin)->generate()) {
            // Begin: ... blocks often replicate under genif/genfor, so
            // suppress duplicate checks.  See t_gen_forif.v for an example.
        } else {
            UINFO(4, "name " << name << endl);  // Not always same as nodep->name
            UINFO(4, "Var1 " << nodep << endl);
            UINFO(4, "Var2 " << fnodep << endl);
            if (nodep->type() == fnodep->type()) {
                nodep->v3error("Duplicate declaration of "
                               << nodeTextType(fnodep) << ": " << AstNode::prettyNameQ(name)
                               << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << fnodep->warnOther() << "... Location of original declaration\n"
                               << fnodep->warnContextSecondary());
            } else {
                nodep->v3error("Unsupported in C: "
                               << ucfirst(nodeTextType(nodep)) << " has the same name as "
                               << nodeTextType(fnodep) << ": " << AstNode::prettyNameQ(name)
                               << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << fnodep->warnOther() << "... Location of original declaration\n"
                               << fnodep->warnContextSecondary());
            }
        }
    }
    void insertDUnit(AstNetlist* nodep) {
        // $unit on top scope
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTdunit se" << cvtToHex(symp) << endl);
        symp->parentp(rootEntp());  // Needed so backward search can find name of top module
        symp->fallbackp(nullptr);
        rootEntp()->insert("$unit ", symp);  // Space so can never name conflict with user code
        //
        UASSERT_OBJ(!m_dunitEntp, nodep, "Call insertDUnit only once");
        m_dunitEntp = symp;
    }
    VSymEnt* insertTopCell(AstNodeModule* nodep, const string& scopename) {
        // Only called on the module at the very top of the hierarchy
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9,
              "      INSERTtop se" << cvtToHex(symp) << "  " << scopename << " " << nodep << endl);
        symp->parentp(rootEntp());  // Needed so backward search can find name of top module
        symp->fallbackp(dunitEntp());  // Needed so can find $unit stuff
        nodep->user1p(symp);
        checkDuplicate(rootEntp(), nodep, nodep->origName());
        rootEntp()->insert(nodep->origName(), symp);
        if (forScopeCreation()) m_nameScopeSymMap.emplace(scopename, symp);
        return symp;
    }
    VSymEnt* insertTopIface(AstCell* nodep, const string& scopename) {
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTtopiface se" << cvtToHex(symp) << "  " << scopename << " " << nodep
                                           << endl);
        symp->parentp(rootEntp());  // Needed so backward search can find name of top module
        symp->fallbackp(dunitEntp());  // Needed so can find $unit stuff
        nodep->user1p(symp);
        if (nodep->modp()) nodep->modp()->user1p(symp);
        checkDuplicate(rootEntp(), nodep, nodep->origName());
        rootEntp()->insert(nodep->origName(), symp);
        if (forScopeCreation()) m_nameScopeSymMap.emplace(scopename, symp);
        return symp;
    }
    VSymEnt* insertCell(VSymEnt* abovep, VSymEnt* modSymp, AstCell* nodep,
                        const string& scopename) {
        UASSERT_OBJ(abovep, nodep, "Null symbol table inserting node");
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTcel se" << cvtToHex(symp) << "  " << scopename << " above=se"
                                      << cvtToHex(abovep) << " mods=se" << cvtToHex(modSymp)
                                      << " node=" << nodep << endl);
        symp->parentp(abovep);
        symp->fallbackp(dunitEntp());  // Needed so can find $unit stuff
        nodep->user1p(symp);
        if (nodep->modp()) nodep->modp()->user1p(symp);
        checkDuplicate(abovep, nodep, nodep->origName());
        abovep->reinsert(nodep->origName(), symp);
        if (forScopeCreation() && abovep != modSymp && !modSymp->findIdFlat(nodep->name())) {
            // If it's foo_DOT_bar, we need to be able to find it under "foo_DOT_bar" too.
            // Duplicates are possible, as until resolve generates might
            // have 2 same cells under an if
            modSymp->reinsert(nodep->name(), symp);
        }
        if (forScopeCreation()) m_nameScopeSymMap.emplace(scopename, symp);
        return symp;
    }
    void insertMap(VSymEnt* symp, const string& scopename) {
        if (forScopeCreation()) m_nameScopeSymMap.emplace(scopename, symp);
    }

    VSymEnt* insertInline(VSymEnt* abovep, VSymEnt* modSymp, AstCellInline* nodep,
                          const string& basename) {
        // A fake point in the hierarchy, corresponding to an inlined module
        // This references to another Sym, and eventually resolves to a module with a prefix
        UASSERT_OBJ(abovep, nodep, "Null symbol table inserting node");
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTinl se" << cvtToHex(symp) << "  " << basename << " above=se"
                                      << cvtToHex(abovep) << " mods=se" << cvtToHex(modSymp)
                                      << " node=" << nodep << endl);
        symp->parentp(abovep);
        symp->fallbackp(modSymp);
        symp->symPrefix(nodep->name() + "__DOT__");
        nodep->user1p(symp);
        checkDuplicate(abovep, nodep, nodep->name());
        abovep->reinsert(basename, symp);
        if (abovep != modSymp && !modSymp->findIdFlat(nodep->name())) {
            // If it's foo_DOT_bar, we need to be able to find it under that too.
            modSymp->reinsert(nodep->name(), symp);
        }
        return symp;
    }
    VSymEnt* insertBlock(VSymEnt* abovep, const string& name, AstNode* nodep,
                         AstNodeModule* classOrPackagep) {
        // A fake point in the hierarchy, corresponding to a begin or function/task block
        // After we remove begins these will go away
        // Note we fallback to the symbol table of the parent, as we want to find variables there
        // However, cells walk the graph, so cells will appear under the begin/ftask itself
        UASSERT_OBJ(abovep, nodep, "Null symbol table inserting node");
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTblk se" << cvtToHex(symp) << "  above=se" << cvtToHex(abovep)
                                      << " pkg=" << cvtToHex(classOrPackagep) << "  node=" << nodep
                                      << endl);
        symp->parentp(abovep);
        symp->classOrPackagep(classOrPackagep);
        symp->fallbackp(abovep);
        nodep->user1p(symp);
        if (name != "") checkDuplicate(abovep, nodep, name);
        // Duplicates are possible, as until resolve generates might have 2 same cells under an if
        abovep->reinsert(name, symp);
        return symp;
    }
    VSymEnt* insertSym(VSymEnt* abovep, const string& name, AstNode* nodep,
                       AstNodeModule* classOrPackagep) {
        UASSERT_OBJ(abovep, nodep, "Null symbol table inserting node");
        VSymEnt* const symp = new VSymEnt{&m_syms, nodep};
        UINFO(9, "      INSERTsym se" << cvtToHex(symp) << "  name='" << name << "' above=se"
                                      << cvtToHex(abovep) << " pkg=" << cvtToHex(classOrPackagep)
                                      << "  node=" << nodep << endl);
        // We don't remember the ent associated with each node, because we
        // need a unique scope entry for each instantiation
        symp->classOrPackagep(classOrPackagep);
        symp->parentp(abovep);
        symp->fallbackp(abovep);
        nodep->user1p(symp);
        checkDuplicate(abovep, nodep, name);
        abovep->reinsert(name, symp);
        return symp;
    }
    static bool existsModScope(AstNodeModule* nodep) { return nodep->user1p() != nullptr; }
    static VSymEnt* getNodeSym(AstNode* nodep) {
        // Don't use this in ResolveVisitor, as we need to pick up the proper
        // reference under each SCOPE
        VSymEnt* const symp = nodep->user1u().toSymEnt();
        UASSERT_OBJ(symp, nodep, "Module/etc never assigned a symbol entry?");
        return symp;
    }
    VSymEnt* getScopeSym(AstScope* nodep) {
        const auto it = m_nameScopeSymMap.find(nodep->name());
        UASSERT_OBJ(it != m_nameScopeSymMap.end(), nodep,
                    "Scope never assigned a symbol entry '" << nodep->name() << "'");
        return it->second;
    }
    void implicitOkAdd(AstNodeModule* nodep, const string& varname) {
        // Mark the given variable name as being allowed to be implicitly declared
        if (nodep) {
            const auto it = m_implicitNameSet.find(std::make_pair(nodep, varname));
            if (it == m_implicitNameSet.end()) m_implicitNameSet.emplace(nodep, varname);
        }
    }
    bool implicitOk(AstNodeModule* nodep, const string& varname) {
        return nodep
               && (m_implicitNameSet.find(std::make_pair(nodep, varname))
                   != m_implicitNameSet.end());
    }

    // Track and later recurse interface modules
    void insertIfaceModSym(AstIface* nodep, VSymEnt* symp) {
        m_ifaceModSyms.emplace_back(nodep, symp);
    }
    void computeIfaceModSyms();

    // Track and later insert interface references
    void insertIfaceVarSym(VSymEnt* symp) {  // Where sym is for a VAR of dtype IFACEREFDTYPE
        m_ifaceVarSyms.push_back(symp);
    }
    // Iface for a raw or arrayed iface
    static AstIfaceRefDType* ifaceRefFromArray(AstNodeDType* nodep) {
        AstIfaceRefDType* ifacerefp = VN_CAST(nodep, IfaceRefDType);
        if (!ifacerefp) {
            if (const AstBracketArrayDType* const arrp = VN_CAST(nodep, BracketArrayDType)) {
                ifacerefp = VN_CAST(arrp->subDTypep(), IfaceRefDType);
            } else if (const AstUnpackArrayDType* const arrp = VN_CAST(nodep, UnpackArrayDType)) {
                ifacerefp = VN_CAST(arrp->subDTypep(), IfaceRefDType);
            }
        }
        return ifacerefp;
    }
    void computeIfaceVarSyms() {
        for (VSymEnt* varSymp : m_ifaceVarSyms) {
            AstVar* const varp = varSymp ? VN_AS(varSymp->nodep(), Var) : nullptr;
            UINFO(9, "  insAllIface se" << cvtToHex(varSymp) << " " << varp << endl);
            AstIfaceRefDType* const ifacerefp = ifaceRefFromArray(varp->subDTypep());
            UASSERT_OBJ(ifacerefp, varp, "Non-ifacerefs on list!");
            if (!ifacerefp->ifaceViaCellp()) {
                if (!ifacerefp->cellp()) {  // Probably a NotFoundModule, or a normal module if
                                            // made mistake
                    UINFO(1, "Associated cell " << AstNode::prettyNameQ(ifacerefp->cellName())
                                                << endl);
                    ifacerefp->v3error("Cannot find file containing interface: "
                                       << AstNode::prettyNameQ(ifacerefp->ifaceName()));
                    continue;
                } else {
                    ifacerefp->v3fatalSrc("Unlinked interface");
                }
            } else if (ifacerefp->ifaceViaCellp()->dead()) {
                if (varp->isIfaceRef()) {
                    ifacerefp->v3error("Parent instance's interface is not found: "
                                       << AstNode::prettyNameQ(ifacerefp->ifaceName()));
                } else {
                    ifacerefp->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: virtual interface never assigned any actual interface");
                    varp->dtypep(ifacerefp->findCHandleDType());
                    VL_DO_DANGLING(ifacerefp->unlinkFrBack()->deleteTree(), ifacerefp);
                }
                continue;
            }
            VSymEnt* const ifaceSymp = getNodeSym(ifacerefp->ifaceViaCellp());
            VSymEnt* ifOrPortSymp = ifaceSymp;
            // Link Modport names to the Modport Node under the Interface
            if (ifacerefp->isModport()) {
                VSymEnt* const foundp = ifaceSymp->findIdFallback(ifacerefp->modportName());
                bool ok = false;
                if (foundp) {
                    if (AstModport* const modportp = VN_CAST(foundp->nodep(), Modport)) {
                        UINFO(4, "Link Modport: " << modportp << endl);
                        ifacerefp->modportp(modportp);
                        ifOrPortSymp = foundp;
                        ok = true;
                    }
                }
                if (!ok) {
                    const string suggest = suggestSymFallback(ifaceSymp, ifacerefp->modportName(),
                                                              LinkNodeMatcherModport{});
                    ifacerefp->modportFileline()->v3error(
                        "Modport not found under interface "
                        << ifacerefp->prettyNameQ(ifacerefp->ifaceName()) << ": "
                        << ifacerefp->prettyNameQ(ifacerefp->modportName()) << '\n'
                        << (suggest.empty() ? "" : ifacerefp->warnMore() + suggest));
                }
            }
            // Alias won't expand until interfaces and modport names are known; see notes at top
            insertScopeAlias(SAMN_IFTOP, varSymp, ifOrPortSymp);
        }
        m_ifaceVarSyms.clear();
    }

    void insertScopeAlias(SAMNum samn, VSymEnt* lhsp, VSymEnt* rhsp) {
        // Track and later insert scope aliases; an interface referenced by
        // a child cell connecting to that interface
        // Typically lhsp=VAR w/dtype IFACEREF, rhsp=IFACE cell
        UINFO(9, "   insertScopeAlias se" << cvtToHex(lhsp) << " se" << cvtToHex(rhsp) << endl);
        UASSERT_OBJ(
            !(VN_IS(rhsp->nodep(), Cell) && !VN_IS(VN_AS(rhsp->nodep(), Cell)->modp(), Iface)),
            rhsp->nodep(), "Got a non-IFACE alias RHS");
        m_scopeAliasMap[samn].emplace(lhsp, rhsp);
    }
    void computeScopeAliases() {
        UINFO(9, "computeIfaceAliases\n");
        for (int samn = 0; samn < SAMN__MAX; ++samn) {
            for (ScopeAliasMap::iterator it = m_scopeAliasMap[samn].begin();
                 it != m_scopeAliasMap[samn].end(); ++it) {
                VSymEnt* const lhsp = it->first;
                VSymEnt* srcp = lhsp;
                while (true) {  // Follow chain of aliases up to highest level non-alias
                    const auto it2 = m_scopeAliasMap[samn].find(srcp);
                    if (it2 != m_scopeAliasMap[samn].end()) {
                        srcp = it2->second;
                        continue;
                    } else {
                        break;
                    }
                }
                UINFO(9, "  iiasa: Insert alias se" << lhsp << " (" << lhsp->nodep()->typeName()
                                                    << ") <- se" << srcp << " " << srcp->nodep()
                                                    << endl);
                // srcp should be an interface reference pointing to the interface we want to
                // import
                lhsp->importFromIface(symsp(), srcp);
                // Allow access to objects not permissible to be listed in a modport
                if (VN_IS(srcp->nodep(), Modport)) {
                    lhsp->importFromIface(symsp(), srcp->parentp(), true);
                }
            }
            // m_scopeAliasMap[samn].clear();  // Done with it, but put into debug file
        }
    }

private:
    VSymEnt* findWithAltFallback(VSymEnt* symp, const string& name, const string& altname) {
        VSymEnt* findp = symp->findIdFallback(name);
        if (findp) return findp;
        if (altname != "") {
            UINFO(8, "     alt fallback\n");
            findp = symp->findIdFallback(altname);
        }
        return findp;
    }

public:
    VSymEnt* findDotted(FileLine* refLocationp, VSymEnt* lookupSymp, const string& dotname,
                        string& baddot, VSymEnt*& okSymp) {
        // Given a dotted hierarchy name, return where in scope it is
        // Note when dotname=="" we just fall through and return lookupSymp
        UINFO(8, "    dottedFind se" << cvtToHex(lookupSymp) << " '" << dotname << "'" << endl);
        bool firstId = true;
        string leftname = dotname;
        okSymp = lookupSymp;  // So can list bad scopes
        while (leftname != "") {  // foreach dotted part of xref name
            string::size_type pos;
            string ident;
            if ((pos = leftname.find('.')) != string::npos) {
                ident = leftname.substr(0, pos);
                leftname = leftname.substr(pos + 1);
            } else {
                ident = leftname;
                leftname = "";
            }
            baddot = ident;  // So user can see where they botched it
            okSymp = lookupSymp;
            string altIdent;
            if (forPrearray()) {
                // GENFOR Begin is foo__BRA__##__KET__ after we've genloop unrolled,
                // but presently should be just "foo".
                // Likewise cell foo__[array] before we've expanded arrays is just foo
                if ((pos = ident.rfind("__BRA__")) != string::npos) {
                    altIdent = ident.substr(0, pos);
                }
            }
            UINFO(8, "         id " << ident << " alt " << altIdent << " left " << leftname
                                    << " at se" << lookupSymp << endl);
            // Spec says; Look at existing module (cellnames then modname),
            // then look up (inst name or modname)
            if (firstId) {
                // Check this module - subcellnames
                const AstCell* cellp = lookupSymp ? VN_CAST(lookupSymp->nodep(), Cell)
                                                  : nullptr;  // Replicated below
                const AstCellInline* inlinep = lookupSymp
                                                   ? VN_CAST(lookupSymp->nodep(), CellInline)
                                                   : nullptr;  // Replicated below
                if (VSymEnt* const findSymp = findWithAltFallback(lookupSymp, ident, altIdent)) {
                    lookupSymp = findSymp;
                }
                // Check this module - cur modname
                else if ((cellp && cellp->modp()->origName() == ident)
                         || (inlinep && inlinep->origModName() == ident)) {
                }
                // $root we walk up to Netlist
                else if (ident == "$root") {
                    lookupSymp = rootEntp();
                    // We've added the '$root' module, now everything else is one lower
                    if (!forPrearray()) {
                        lookupSymp = lookupSymp->findIdFlat(ident);
                        UASSERT(lookupSymp, "Cannot find $root module under netlist");
                    }
                }
                // Move up and check cellname + modname
                else {
                    bool crossedCell = false;  // Crossed a cell boundary
                    while (lookupSymp) {
                        lookupSymp = lookupSymp->parentp();
                        cellp = lookupSymp ? VN_CAST(lookupSymp->nodep(), Cell)
                                           : nullptr;  // Replicated above
                        inlinep = lookupSymp ? VN_CAST(lookupSymp->nodep(), CellInline)
                                             : nullptr;  // Replicated above
                        if (lookupSymp) {
                            UINFO(9, "    Up to " << lookupSymp << endl);
                            if (cellp || inlinep) crossedCell = true;
                            if ((cellp && cellp->modp()->origName() == ident)
                                || (inlinep && inlinep->origModName() == ident)) {
                                break;
                            } else if (VSymEnt* const findSymp
                                       = findWithAltFallback(lookupSymp, ident, altIdent)) {
                                lookupSymp = findSymp;
                                if (crossedCell && VN_IS(lookupSymp->nodep(), Var)) {
                                    UINFO(9, "    Not found but matches var name in parent "
                                                 << lookupSymp << endl);
                                    return nullptr;
                                }
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    if (!lookupSymp) return nullptr;  // Not found
                }
            } else {  // Searching for middle submodule, must be a cell name
                if (VSymEnt* const findSymp = findWithAltFallback(lookupSymp, ident, altIdent)) {
                    lookupSymp = findSymp;
                } else {
                    return nullptr;  // Not found
                }
            }
            if (lookupSymp) {
                if (const AstCell* const cellp = VN_CAST(lookupSymp->nodep(), Cell)) {
                    if (const AstNodeModule* const modp = cellp->modp()) {
                        if (modp->hierBlock()) {
                            refLocationp->v3error("Cannot access inside hierarchical block");
                        } else if (VN_IS(modp, NotFoundModule)) {
                            refLocationp->v3error("Dotted reference to instance that refers to "
                                                  "missing module/interface: "
                                                  << modp->prettyNameQ());
                        }
                    }
                }
            }
            firstId = false;
        }
        return lookupSymp;
    }

    static string removeLastInlineScope(const string& name) {
        string out = name;
        const string dot = "__DOT__";
        const size_t dotPos = out.rfind(dot, out.size() - dot.length() - 2);
        if (dotPos == string::npos) {
            return "";
        } else {
            return out.erase(dotPos + dot.length(), string::npos);
        }
    }

    VSymEnt* findSymPrefixed(VSymEnt* lookupSymp, const string& dotname, string& baddot) {
        // Find symbol in given point in hierarchy, allowing prefix (post-Inline)
        // For simplicity lookupSymp may be passed nullptr result from findDotted
        if (!lookupSymp) return nullptr;
        UINFO(8, "    findSymPrefixed "
                     << dotname << " under se" << cvtToHex(lookupSymp)
                     << ((lookupSymp->symPrefix() == "") ? "" : " as ")
                     << ((lookupSymp->symPrefix() == "") ? "" : lookupSymp->symPrefix() + dotname)
                     << "  at se" << lookupSymp << endl);
        string prefix = lookupSymp->symPrefix();
        VSymEnt* foundp = nullptr;
        while (!foundp) {
            foundp = lookupSymp->findIdFallback(prefix + dotname);  // Might be nullptr
            if (prefix.empty()) break;
            const string nextPrefix = removeLastInlineScope(prefix);
            if (prefix == nextPrefix) break;
            prefix = nextPrefix;
        }
        if (!foundp) baddot = dotname;
        return foundp;
    }
    string suggestSymFallback(VSymEnt* lookupSymp, const string& name,
                              const VNodeMatcher& matcher) {
        // Suggest alternative symbol in given point in hierarchy
        // Does not support inline, as we find user-level errors before inlining
        // For simplicity lookupSymp may be passed nullptr result from findDotted
        if (!lookupSymp) return "";
        VSpellCheck speller;
        lookupSymp->candidateIdFallback(&speller, &matcher);
        return speller.bestCandidateMsg(name);
    }
    string suggestSymFlat(VSymEnt* lookupSymp, const string& name, const VNodeMatcher& matcher) {
        if (!lookupSymp) return "";
        VSpellCheck speller;
        lookupSymp->candidateIdFlat(&speller, &matcher);
        return speller.bestCandidateMsg(name);
    }
};

LinkDotState* LinkDotState::s_errorThisp = nullptr;

//======================================================================

class LinkDotFindVisitor final : public VNVisitor {
    // STATE
    LinkDotState* const m_statep;  // State to pass between visitors, including symbol table
    AstNodeModule* m_classOrPackagep = nullptr;  // Current package
    AstClocking* m_clockingp = nullptr;  // Current clocking block
    VSymEnt* m_modSymp = nullptr;  // Symbol Entry for current module
    VSymEnt* m_curSymp = nullptr;  // Symbol Entry for current table, where to lookup/insert
    string m_scope;  // Scope text
    const AstNodeBlock* m_blockp = nullptr;  // Current Begin/end block
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    bool m_inRecursion = false;  // Inside a recursive module
    int m_paramNum = 0;  // Parameter number, for position based connection
    bool m_explicitNew = false;  // Hit a "new" function
    int m_modBlockNum = 0;  // Begin block number in module, 0=none seen
    int m_modWithNum = 0;  // With block number, 0=none seen

    // METHODS
    void makeImplicitNew(AstClass* nodep) {
        AstFunc* const newp = new AstFunc{nodep->fileline(), "new", nullptr, nullptr};
        // If needed, super.new() call is added the 2nd pass of V3LinkDotResolve,
        // because base classes are already resolved there.
        newp->isConstructor(true);
        nodep->addMembersp(newp);
        UINFO(8, "Made implicit new for " << nodep->name() << ": " << nodep << endl);
        m_statep->insertBlock(m_curSymp, newp->name(), newp, m_classOrPackagep);
    }

    bool isHierBlockWrapper(const string& name) const {
        const V3HierBlockOptSet& hierBlocks = v3Global.opt.hierBlocks();
        return hierBlocks.find(name) != hierBlocks.end();
    }

    // VISITs
    void visit(AstNetlist* nodep) override {
        // Process $unit or other packages
        // Not needed - dotted references not allowed from inside packages
        // for (AstNodeModule* nodep = v3Global.rootp()->modulesp();
        //     nodep; nodep=VN_AS(nodep->nextp(), NodeModule)) {
        //    if (VN_IS(nodep, Package)) {}}

        m_statep->insertDUnit(nodep);

        // First back iterate, to find all packages. Backward as must do base
        // packages before using packages
        iterateChildrenBackwardsConst(nodep);

        // The first modules in the list are always the top modules
        // (sorted before this is called).
        // This may not be the module with isTop() set, as early in the steps,
        // wrapTop may have not been created yet.
        if (!nodep->modulesp()) nodep->v3error("No top level module found");
        for (AstNodeModule* modp = nodep->modulesp(); modp && modp->level() <= 2;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            UINFO(8, "Top Module: " << modp << endl);
            m_scope = "TOP";

            if (m_statep->forPrearray() && v3Global.opt.topIfacesSupported()) {
                for (AstNode* subnodep = modp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
                    if (AstVar* const varp = VN_CAST(subnodep, Var)) {
                        if (varp->isIfaceRef()) {
                            const AstNodeDType* const subtypep = varp->subDTypep();
                            const AstIfaceRefDType* ifacerefp = nullptr;
                            if (VN_IS(subtypep, IfaceRefDType)) {
                                ifacerefp = VN_AS(varp->subDTypep(), IfaceRefDType);
                            } else if (VN_IS(subtypep, BracketArrayDType)) {
                                const AstBracketArrayDType* const arrp
                                    = VN_AS(subtypep, BracketArrayDType);
                                const AstNodeDType* const arrsubtypep = arrp->subDTypep();
                                if (VN_IS(arrsubtypep, IfaceRefDType)) {
                                    ifacerefp = VN_AS(arrsubtypep, IfaceRefDType);
                                }
                            } else if (VN_IS(subtypep, UnpackArrayDType)) {
                                const AstUnpackArrayDType* const arrp
                                    = VN_AS(subtypep, UnpackArrayDType);
                                const AstNodeDType* const arrsubtypep = arrp->subDTypep();
                                if (VN_IS(arrsubtypep, IfaceRefDType)) {
                                    ifacerefp = VN_AS(arrsubtypep, IfaceRefDType);
                                }
                            }

                            if (ifacerefp && !ifacerefp->cellp()) {
                                // A dummy cell to keep the top level interface alive and correctly
                                // optimized for default parameter values
                                AstCell* ifacecellp
                                    = new AstCell{nodep->fileline(),
                                                  nodep->fileline(),
                                                  modp->name() + "__02E" + varp->name(),
                                                  ifacerefp->ifaceName(),
                                                  nullptr,
                                                  nullptr,
                                                  nullptr};
                                ifacecellp->modp(ifacerefp->ifacep());
                                m_curSymp = m_modSymp
                                    = m_statep->insertTopIface(ifacecellp, m_scope);
                                { iterate(ifacecellp); }
                            }
                        }
                    }
                }
            }

            m_curSymp = m_modSymp = m_statep->insertTopCell(modp, m_scope);
            { iterate(modp); }

            m_scope = "";
            m_curSymp = m_modSymp = nullptr;
        }
    }
    void visit(AstTypeTable*) override {}
    void visit(AstConstPool*) override {}
    void visit(AstNodeModule* nodep) override {
        // Called on top module from Netlist, other modules from the cell creating them,
        // and packages
        UINFO(8, "   " << nodep << endl);
        // m_curSymp/m_modSymp maybe nullptr for packages and non-top modules
        // Packages will be under top after the initial phases, but until then
        // need separate handling
        const bool standalonePkg
            = !m_modSymp && (m_statep->forPrearray() && VN_IS(nodep, Package));
        const bool doit = (m_modSymp || standalonePkg);
        VL_RESTORER(m_scope);
        VL_RESTORER(m_classOrPackagep);
        VL_RESTORER(m_modSymp);
        VL_RESTORER(m_curSymp);
        VL_RESTORER(m_paramNum);
        VL_RESTORER(m_modBlockNum);
        VL_RESTORER(m_modWithNum);
        if (doit && nodep->user2()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Identically recursive module (module instantiates "
                          "itself, without changing parameters): "
                              << AstNode::prettyNameQ(nodep->origName()));
        } else if (doit) {
            UINFO(4, "     Link Module: " << nodep << endl);
            UASSERT_OBJ(!nodep->dead(), nodep, "Module in instance tree mislabeled as dead?");
            AstPackage* const pkgp = VN_CAST(nodep, Package);
            m_classOrPackagep = pkgp;
            if (standalonePkg) {
                if (pkgp->isDollarUnit()) {
                    m_curSymp = m_modSymp = m_statep->dunitEntp();
                    nodep->user1p(m_curSymp);
                } else {
                    VSymEnt* const upperSymp = m_statep->dunitEntp();
                    m_scope = nodep->name();
                    m_curSymp = m_modSymp = m_statep->insertBlock(
                        upperSymp, nodep->name() + "::", nodep, m_classOrPackagep);
                    UINFO(9, "New module scope " << m_curSymp << endl);
                }
            }
            //
            m_paramNum = 0;
            m_modBlockNum = 0;
            m_modWithNum = 0;
            // m_modSymp/m_curSymp for non-packages set by AstCell above this module
            // Iterate
            nodep->user2(true);
            iterateChildren(nodep);
            nodep->user2(false);
            nodep->user4(true);
            // Interfaces need another pass when signals are resolved
            if (AstIface* const ifacep = VN_CAST(nodep, Iface)) {
                m_statep->insertIfaceModSym(ifacep, m_curSymp);
            }
        } else if (isHierBlockWrapper(nodep->name())) {
            UINFO(5, "Module is hierarchical block, must not be dead: " << nodep << endl);
            m_scope = nodep->name();
            VSymEnt* const upperSymp = m_curSymp ? m_curSymp : m_statep->rootEntp();
            m_curSymp = m_modSymp
                = m_statep->insertBlock(upperSymp, nodep->name() + "::", nodep, m_classOrPackagep);
            iterateChildren(nodep);
            nodep->user4(true);
        } else {  // !doit
            // Will be optimized away later
            // Can't remove now, as our backwards iterator will throw up
            UINFO(5, "Module not under any CELL or top - dead module: " << nodep << endl);
        }
    }
    void visit(AstClass* nodep) override {
        UASSERT_OBJ(m_curSymp, nodep, "Class not under module/package/$unit");
        UINFO(8, "   " << nodep << endl);
        VL_RESTORER(m_scope);
        VL_RESTORER(m_classOrPackagep);
        VL_RESTORER(m_modSymp);
        VL_RESTORER(m_curSymp);
        VL_RESTORER(m_paramNum);
        VL_RESTORER(m_modBlockNum);
        VL_RESTORER(m_modWithNum);
        {
            UINFO(4, "     Link Class: " << nodep << endl);
            VSymEnt* const upperSymp = m_curSymp;
            m_scope = m_scope + "." + nodep->name();
            m_classOrPackagep = nodep;
            m_curSymp = m_modSymp
                = m_statep->insertBlock(upperSymp, nodep->name(), nodep, m_classOrPackagep);
            m_statep->insertMap(m_curSymp, m_scope);
            UINFO(9, "New module scope " << m_curSymp << endl);
            //
            m_paramNum = 0;
            m_modBlockNum = 0;
            m_modWithNum = 0;
            m_explicitNew = false;
            // m_modSymp/m_curSymp for non-packages set by AstCell above this module
            // Iterate
            iterateChildren(nodep);
            nodep->user4(true);
            // Implicit new needed?
            if (!m_explicitNew && m_statep->forPrimary()) makeImplicitNew(nodep);
        }
    }
    void visit(AstScope* nodep) override {
        UASSERT_OBJ(m_statep->forScopeCreation(), nodep,
                    "Scopes should only exist right after V3Scope");
        // Ignored.  Processed in next step
    }
    void visit(AstCell* nodep) override {
        UINFO(5, "   CELL under " << m_scope << " is " << nodep << endl);
        // Process XREFs/etc inside pins
        if (nodep->recursive() && m_inRecursion) return;
        iterateChildren(nodep);
        // Recurse in, preserving state
        VL_RESTORER(m_scope);
        VL_RESTORER(m_blockp);
        VL_RESTORER(m_modSymp);
        VL_RESTORER(m_curSymp);
        VL_RESTORER(m_paramNum);
        VL_RESTORER(m_inRecursion);
        // Where do we add it?
        VSymEnt* aboveSymp = m_curSymp;
        const string origname = AstNode::dedotName(nodep->name());
        string::size_type pos;
        if ((pos = origname.rfind('.')) != string::npos) {
            // Flattened, find what CellInline it should live under
            const string scope = origname.substr(0, pos);
            string baddot;
            VSymEnt* okSymp;
            aboveSymp = m_statep->findDotted(nodep->fileline(), aboveSymp, scope, baddot, okSymp);
            UASSERT_OBJ(aboveSymp, nodep,
                        "Can't find instance insertion point at "
                            << AstNode::prettyNameQ(baddot) << " in: " << nodep->prettyNameQ());
        }
        {
            m_scope = m_scope + "." + nodep->name();
            m_curSymp = m_modSymp = m_statep->insertCell(aboveSymp, m_modSymp, nodep, m_scope);
            m_blockp = nullptr;
            m_inRecursion = nodep->recursive();
            // We don't report NotFoundModule, as may be a unused module in a generate
            if (nodep->modp()) iterate(nodep->modp());
        }
    }
    void visit(AstCellInline* nodep) override {
        UINFO(5, "   CELLINLINE under " << m_scope << " is " << nodep << endl);
        VSymEnt* aboveSymp = m_curSymp;
        // If baz__DOT__foo__DOT__bar, we need to find baz__DOT__foo and add bar to it.
        const string dottedname = nodep->name();
        string::size_type pos;
        if ((pos = dottedname.rfind("__DOT__")) != string::npos) {
            const string dotted = dottedname.substr(0, pos);
            const string ident = dottedname.substr(pos + std::strlen("__DOT__"));
            string baddot;
            VSymEnt* okSymp;
            aboveSymp = m_statep->findDotted(nodep->fileline(), aboveSymp, dotted, baddot, okSymp);
            UASSERT_OBJ(aboveSymp, nodep,
                        "Can't find cellinline insertion point at "
                            << AstNode::prettyNameQ(baddot) << " in: " << nodep->prettyNameQ());
            m_statep->insertInline(aboveSymp, m_modSymp, nodep, ident);
        } else {  // No __DOT__, just directly underneath
            m_statep->insertInline(aboveSymp, m_modSymp, nodep, nodep->name());
        }
    }
    void visit(AstDefParam* nodep) override {
        nodep->user1p(m_curSymp);
        iterateChildren(nodep);
    }
    void visit(AstNodeBlock* nodep) override {
        UINFO(5, "   " << nodep << endl);
        if (nodep->name() == "" && nodep->unnamed()) {
            // Unnamed blocks are only important when they contain var
            // decls, so search for them. (Otherwise adding all the
            // unnamed#'s would just confuse tracing variables in
            // places such as tasks, where "task ...; begin ... end"
            // are common.
            for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (VN_IS(stmtp, Var) || VN_IS(stmtp, Foreach)) {
                    std::string name;
                    const std::string stepStr = m_statep->forPrimary()
                                                    ? ""
                                                    : std::to_string(m_statep->stepNumber()) + "_";
                    do {
                        ++m_modBlockNum;
                        name = "unnamedblk" + stepStr + cvtToStr(m_modBlockNum);
                        // Increment again if earlier pass of V3LinkDot claimed this name
                    } while (m_curSymp->findIdFlat(name));
                    nodep->name(name);
                    break;
                }
            }
        }
        if (nodep->name() == "") {
            iterateChildren(nodep);
        } else {
            VL_RESTORER(m_blockp);
            VL_RESTORER(m_curSymp);
            {
                m_blockp = nodep;
                m_curSymp
                    = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
                m_curSymp->fallbackp(VL_RESTORER_PREV(m_curSymp));
                // Iterate
                iterateChildren(nodep);
            }
        }
    }
    void visit(AstNodeFTask* nodep) override {
        // NodeTask: Remember its name for later resolution
        UINFO(5, "   " << nodep << endl);
        UASSERT_OBJ(m_curSymp && m_modSymp, nodep, "Function/Task not under module?");
        if (nodep->name() == "new") m_explicitNew = true;
        // Remember the existing symbol table scope
        VL_RESTORER(m_classOrPackagep);
        VL_RESTORER(m_curSymp);
        VSymEnt* upSymp = m_curSymp;
        {
            if (VN_IS(m_curSymp->nodep(), Class)
                && VN_AS(m_curSymp->nodep(), Class)->isInterfaceClass() && !nodep->pureVirtual()
                && !nodep->isConstructor()) {
                nodep->v3error("Interface class functions must be pure virtual"
                               << " (IEEE 1800-2017 8.26): " << nodep->prettyNameQ());
            }
            // Change to appropriate package if extern declaration (vs definition)
            if (nodep->classOrPackagep()) {
                AstClassOrPackageRef* const cpackagerefp
                    = VN_CAST(nodep->classOrPackagep(), ClassOrPackageRef);
                if (!cpackagerefp) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: extern function definition with class-in-class");
                } else {
                    AstClass* const classp = VN_CAST(cpackagerefp->classOrPackagep(), Class);
                    if (!classp) {
                        nodep->v3error("Extern declaration's scope is not a defined class");
                    } else {
                        m_curSymp = m_statep->getNodeSym(classp);
                        upSymp = m_curSymp;
                        if (!nodep->isExternDef()) {
                            // Move it to proper spot under the target class
                            nodep->unlinkFrBack();
                            classp->addStmtsp(nodep);
                            nodep->isExternDef(true);  // So we check there's a matching extern
                            nodep->classOrPackagep()->unlinkFrBack()->deleteTree();
                        }
                    }
                }
            }
            // Set the class as package for iteration
            if (VN_IS(m_curSymp->nodep(), Class)) {
                m_classOrPackagep = VN_AS(m_curSymp->nodep(), Class);
            }
            // Create symbol table for the task's vars
            const string name
                = std::string{nodep->isExternProto() ? "extern " : ""} + nodep->name();
            m_curSymp = m_statep->insertBlock(m_curSymp, name, nodep, m_classOrPackagep);
            m_curSymp->fallbackp(upSymp);
            // Convert the func's range to the output variable
            // This should probably be done in the Parser instead, as then we could
            // just attach normal signal attributes to it.
            if (!nodep->isExternProto() && nodep->fvarp() && !VN_IS(nodep->fvarp(), Var)) {
                AstNodeDType* dtypep = VN_CAST(nodep->fvarp(), NodeDType);
                // If unspecified, function returns one bit; however when we
                // support NEW() it could also return the class reference.
                if (dtypep) {
                    dtypep->unlinkFrBack();
                } else {
                    dtypep = new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::LOGIC};
                }
                AstVar* const newvarp
                    = new AstVar{nodep->fileline(), VVarType::VAR, nodep->name(),
                                 VFlagChildDType{}, dtypep};  // Not dtype resolved yet
                newvarp->direction(VDirection::OUTPUT);
                newvarp->lifetime(VLifetime::AUTOMATIC);
                newvarp->funcReturn(true);
                newvarp->trace(false);  // Not user visible
                newvarp->attrIsolateAssign(nodep->attrIsolateAssign());
                nodep->fvarp(newvarp);
                // Explicit insert required, as the var name shadows the upper level's task name
                m_statep->insertSym(m_curSymp, newvarp->name(), newvarp,
                                    nullptr /*classOrPackagep*/);
            }
            VL_RESTORER(m_ftaskp);
            m_ftaskp = nodep;
            iterateChildren(nodep);
        }
    }
    void visit(AstClocking* nodep) override {
        VL_RESTORER(m_clockingp);
        m_clockingp = nodep;
        iterate(nodep->sensesp());
        iterateAndNextNull(nodep->itemsp());
        // If the block has no name, one cannot reference the clockvars
        VSymEnt* itSymp = nullptr;
        if (nodep->isGlobal()  //
            && m_statep->forPrimary()) {  // else flattening may see two globals
            m_statep->checkDuplicate(m_curSymp, nodep, "__024global_clock");
            itSymp
                = m_statep->insertBlock(m_curSymp, "__024global_clock", nodep, m_classOrPackagep);
            itSymp->fallbackp(nullptr);
        }
        if (!nodep->name().empty()) {
            itSymp = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
            itSymp->fallbackp(nullptr);
        }
        if (itSymp) {
            VL_RESTORER(m_curSymp);
            m_curSymp = itSymp;
            iterateAndNextNull(nodep->itemsp());
        }
    }
    void visit(AstClockingItem* nodep) override {
        if (nodep->varp()) {
            if (m_curSymp->nodep() == m_clockingp) iterate(nodep->varp());
            return;
        }
        std::string varname;
        AstNodeDType* dtypep;
        if (AstAssign* const assignp = nodep->assignp()) {
            AstNodeExpr* const rhsp = assignp->rhsp()->unlinkFrBack();
            dtypep = new AstRefDType{nodep->fileline(), AstRefDType::FlagTypeOfExpr{},
                                     rhsp->cloneTree(false)};
            nodep->exprp(rhsp);
            varname = assignp->lhsp()->name();
            VL_DO_DANGLING(assignp->unlinkFrBack()->deleteTree(), assignp);
        } else {
            AstNodeExpr* const refp = nodep->exprp();
            const VSymEnt* foundp = m_curSymp->findIdFallback(refp->name());
            if (!foundp || !foundp->nodep()) {
                refp->v3error("Corresponding variable " << refp->prettyNameQ()
                                                        << " does not exist");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                return;
            }
            varname = refp->name();
            dtypep = VN_AS(foundp->nodep(), Var)->childDTypep()->cloneTree(false);
        }
        AstVar* const newvarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, varname,
                                           VFlagChildDType{}, dtypep};
        newvarp->lifetime(VLifetime::STATIC);
        nodep->varp(newvarp);
        iterate(nodep->exprp());
    }
    void visit(AstConstraint* nodep) override {
        VL_RESTORER(m_curSymp);
        m_curSymp = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        // Var: Remember its name for later resolution
        UASSERT_OBJ(m_curSymp && m_modSymp, nodep, "Var not under module?");
        iterateChildren(nodep);
        if (VN_IS(m_curSymp->nodep(), Class)
            && VN_AS(m_curSymp->nodep(), Class)->isInterfaceClass() && !nodep->isParam()) {
            nodep->v3error("Interface class cannot contain non-parameter members"
                           << " (IEEE 1800-2017 8.26): " << nodep->prettyNameQ());
        }
        if (!m_statep->forScopeCreation()) {
            // Find under either a task or the module's vars
            const VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
            if (!foundp && m_modSymp && nodep->name() == m_modSymp->nodep()->name()) {
                foundp = m_modSymp;  // Conflicts with modname?
            }
            AstVar* const findvarp = foundp ? VN_CAST(foundp->nodep(), Var) : nullptr;
            bool ins = false;
            if (!foundp) {
                ins = true;
            } else if (!findvarp && m_curSymp->findIdFlat(nodep->name())) {
                nodep->v3error("Unsupported in C: Variable has same name as "
                               << LinkDotState::nodeTextType(foundp->nodep()) << ": "
                               << nodep->prettyNameQ());
            } else if (findvarp != nodep) {
                UINFO(4, "DupVar: " << nodep << " ;; " << foundp->nodep() << endl);
                UINFO(4, "    found  cur=se" << cvtToHex(m_curSymp) << " ;; parent=se"
                                             << cvtToHex(foundp->parentp()) << endl);
                if (foundp->parentp() == m_curSymp  // Only when on same level
                    && !foundp->imported()) {  // and not from package
                    if (VN_IS(m_curSymp->nodep(), Clocking)) {
                        nodep->v3error("Multiple clockvars with the same name not allowed");
                        return;
                    }
                    const bool nansiBad
                        = (((findvarp->isDeclTyped() || findvarp->isNet())
                            && (nodep->isDeclTyped() || nodep->isNet()))
                           || (findvarp->isIO() && nodep->isIO()));  // e.g. !(output && output)
                    const bool ansiBad
                        = findvarp->isAnsi() || nodep->isAnsi();  // dup illegal with ANSI
                    if (ansiBad || nansiBad) {
                        bool ansiWarn = ansiBad && !nansiBad;
                        if (ansiWarn) {
                            static int didAnsiWarn = false;
                            if (didAnsiWarn++) ansiWarn = false;
                        }
                        nodep->v3error("Duplicate declaration of signal: "
                                       << nodep->prettyNameQ() << '\n'
                                       << (ansiWarn ? nodep->warnMore()
                                                          + "... note: ANSI ports must have"
                                                            " type declared with the I/O"
                                                            " (IEEE 1800-2017 23.2.2.2)\n"
                                                    : "")
                                       << nodep->warnContextPrimary() << '\n'
                                       << findvarp->warnOther()
                                       << "... Location of original declaration\n"
                                       << findvarp->warnContextSecondary());
                        // Combining most likely reduce other errors
                        findvarp->combineType(nodep);
                        findvarp->fileline()->modifyStateInherit(nodep->fileline());
                    } else {
                        findvarp->combineType(nodep);
                        findvarp->fileline()->modifyStateInherit(nodep->fileline());
                        if (nodep->getChildDTypep()->numeric().isSigned()
                            && !findvarp->getChildDTypep()->numeric().isSigned()) {
                            findvarp->getChildDTypep()->numeric(VSigning{true});
                        }
                        AstBasicDType* const bdtypep
                            = VN_CAST(findvarp->childDTypep(), BasicDType);
                        if (bdtypep && bdtypep->implicit()) {
                            // Then have "input foo" and "real foo" so the
                            // dtype comes from the other side.
                            AstNodeDType* const newdtypep = nodep->subDTypep();
                            UASSERT_OBJ(newdtypep && nodep->childDTypep(), findvarp,
                                        "No child type?");
                            VL_DO_DANGLING(bdtypep->unlinkFrBack()->deleteTree(), bdtypep);
                            newdtypep->unlinkFrBack();
                            findvarp->childDTypep(newdtypep);
                        }
                    }
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                } else {
                    // User can disable the message at either point
                    if (!(m_ftaskp && m_ftaskp->dpiImport())
                        && (!m_ftaskp || m_ftaskp != foundp->nodep())  // Not the function's
                                                                       // variable hiding function
                        && !nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
                        && !foundp->nodep()->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
                        nodep->v3warn(VARHIDDEN,
                                      "Declaration of signal hides declaration in upper scope: "
                                          << nodep->prettyNameQ() << '\n'
                                          << nodep->warnContextPrimary() << '\n'
                                          << foundp->nodep()->warnOther()
                                          << "... Location of original declaration\n"
                                          << foundp->nodep()->warnContextSecondary());
                    }
                    ins = true;
                }
            }
            if (ins) {
                if (m_statep->forPrimary() && nodep->isGParam()
                    && VN_IS(m_modSymp->nodep(), Module)
                    && (m_statep->rootEntp()->nodep() == m_modSymp->parentp()->nodep())) {
                    // This is the toplevel module. Check for command line overwrites of parameters
                    // We first search if the parameter is overwritten and then replace it with a
                    // new value.
                    if (v3Global.opt.hasParameter(nodep->name())) {
                        const string svalue = v3Global.opt.parameter(nodep->name());
                        if (AstConst* const valuep
                            = AstConst::parseParamLiteral(nodep->fileline(), svalue)) {
                            UINFO(9, "       replace parameter " << nodep << endl);
                            UINFO(9, "       with " << valuep << endl);
                            if (nodep->valuep()) pushDeletep(nodep->valuep()->unlinkFrBack());
                            nodep->valuep(valuep);
                        }
                    }
                }
                VSymEnt* const insp
                    = m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
                if (m_statep->forPrimary() && nodep->isGParam()) {
                    ++m_paramNum;
                    VSymEnt* const symp
                        = m_statep->insertSym(m_curSymp, "__paramNumber" + cvtToStr(m_paramNum),
                                              nodep, m_classOrPackagep);
                    symp->exported(false);
                }
                AstIfaceRefDType* const ifacerefp
                    = LinkDotState::ifaceRefFromArray(nodep->subDTypep());
                if (ifacerefp) {
                    // Can't resolve until interfaces and modport names are
                    // known; see notes at top
                    m_statep->insertIfaceVarSym(insp);
                }
            }
        }
    }
    void visit(AstTypedef* nodep) override {
        UASSERT_OBJ(m_curSymp, nodep, "Typedef not under module/package/$unit");
        iterateChildren(nodep);
        m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
    }
    void visit(AstTypedefFwd* nodep) override {
        UASSERT_OBJ(m_curSymp, nodep, "Typedef not under module/package/$unit");
        iterateChildren(nodep);
        // No need to insert, only the real typedef matters, but need to track for errors
        nodep->user1p(m_curSymp);
    }
    void visit(AstParamTypeDType* nodep) override {
        UASSERT_OBJ(m_curSymp, nodep, "Parameter type not under module/package/$unit");
        iterateChildren(nodep);
        m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
        if (m_statep->forPrimary() && nodep->isGParam()) {
            ++m_paramNum;
            VSymEnt* const symp = m_statep->insertSym(
                m_curSymp, "__paramNumber" + cvtToStr(m_paramNum), nodep, m_classOrPackagep);
            symp->exported(false);
        }
    }
    void visit(AstCFunc* nodep) override {
        // For dotted resolution, ignore all AstVars under functions, otherwise shouldn't exist
        UASSERT_OBJ(!m_statep->forScopeCreation(), nodep, "No CFuncs expected in tree yet");
    }
    void visit(AstEnumItem* nodep) override {
        // EnumItem: Remember its name for later resolution
        iterateChildren(nodep);
        // Find under either a task or the module's vars
        const VSymEnt* foundp = m_curSymp->findIdFallback(nodep->name());
        if (!foundp && m_modSymp && nodep->name() == m_modSymp->nodep()->name()) {
            foundp = m_modSymp;  // Conflicts with modname?
        }
        AstEnumItem* const findvarp = foundp ? VN_CAST(foundp->nodep(), EnumItem) : nullptr;
        bool ins = false;
        if (!foundp) {
            ins = true;
        } else if (findvarp != nodep) {
            UINFO(4, "DupVar: " << nodep << " ;; " << foundp << endl);
            if (foundp->parentp() == m_curSymp  // Only when on same level
                && !foundp->imported()) {  // and not from package
                nodep->v3error("Duplicate declaration of enum value: "
                               << nodep->prettyName() << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << foundp->nodep()->warnOther()
                               << "... Location of original declaration\n"
                               << foundp->nodep()->warnContextSecondary());
            } else {
                // User can disable the message at either point
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
                    && !foundp->nodep()->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
                    nodep->v3warn(VARHIDDEN,
                                  "Declaration of enum value hides declaration in upper scope: "
                                      << nodep->prettyName() << '\n'
                                      << nodep->warnContextPrimary() << '\n'
                                      << foundp->nodep()->warnOther()
                                      << "... Location of original declaration\n"
                                      << foundp->nodep()->warnContextSecondary());
                }
                ins = true;
            }
        }
        if (ins) m_statep->insertSym(m_curSymp, nodep->name(), nodep, m_classOrPackagep);
    }
    void visit(AstPackageImport* nodep) override {
        UINFO(4, "  Link: " << nodep << endl);
        VSymEnt* const srcp = m_statep->getNodeSym(nodep->packagep());
        if (nodep->name() == "*") {
            if (nodep->packagep() != v3Global.rootp()->stdPackagep()) {
                if (m_curSymp == m_statep->dunitEntp()) {
                    nodep->v3warn(IMPORTSTAR,
                                  "Import::* in $unit scope may pollute global namespace");
                }
            }
        } else {
            VSymEnt* const impp = srcp->findIdFlat(nodep->name());
            if (!impp) {
                nodep->v3error("Import object not found: '" << nodep->packagep()->prettyName()
                                                            << "::" << nodep->prettyName() << "'");
            }
        }
        m_curSymp->importFromPackage(m_statep->symsp(), srcp, nodep->name());
        UINFO(9, "    Link Done: " << nodep << endl);
        // No longer needed, but can't delete until any multi-instantiated modules are expanded
    }
    void visit(AstPackageExport* nodep) override {
        UINFO(9, "  Link: " << nodep << endl);
        VSymEnt* const srcp = m_statep->getNodeSym(nodep->packagep());
        if (nodep->name() != "*") {
            VSymEnt* const impp = srcp->findIdFlat(nodep->name());
            if (!impp) {
                nodep->v3error("Export object not found: '" << nodep->packagep()->prettyName()
                                                            << "::" << nodep->prettyName() << "'");
            }
        }
        m_curSymp->exportFromPackage(m_statep->symsp(), srcp, nodep->name());
        UINFO(9, "    Link Done: " << nodep << endl);
        // No longer needed, but can't delete until any multi-instantiated modules are expanded
    }
    void visit(AstPackageExportStarStar* nodep) override {
        UINFO(4, "  Link: " << nodep << endl);
        m_curSymp->exportStarStar(m_statep->symsp());
        // No longer needed, but can't delete until any multi-instantiated modules are expanded
    }

    void visit(AstNodeForeach* nodep) override {
        // Symbol table needs nodep->name() as the index variable's name
        VL_RESTORER(m_curSymp);
        {
            ++m_modWithNum;
            m_curSymp = m_statep->insertBlock(m_curSymp, "__Vforeach" + cvtToStr(m_modWithNum),
                                              nodep, m_classOrPackagep);
            m_curSymp->fallbackp(VL_RESTORER_PREV(m_curSymp));
            // DOT(x, SELLOOPVARS(var, loops)) -> SELLOOPVARS(DOT(x, var), loops)
            if (AstDot* const dotp = VN_CAST(nodep->arrayp(), Dot)) {
                if (AstSelLoopVars* const loopvarsp = VN_CAST(dotp->rhsp(), SelLoopVars)) {
                    AstNodeExpr* const fromp = loopvarsp->fromp()->unlinkFrBack();
                    loopvarsp->unlinkFrBack();
                    dotp->replaceWith(loopvarsp);
                    dotp->rhsp(fromp);
                    loopvarsp->fromp(dotp);
                }
            }
            const auto loopvarsp = VN_CAST(nodep->arrayp(), SelLoopVars);
            if (!loopvarsp) {
                AstNode* const warnp = nodep->arrayp() ? nodep->arrayp() : nodep;
                warnp->v3warn(E_UNSUPPORTED,
                              "Unsupported (or syntax error): Foreach on this array's construct");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                return;
            }
            for (AstNode *nextp, *argp = loopvarsp->elementsp(); argp; argp = nextp) {
                nextp = argp->nextp();
                AstVar* argrefp = nullptr;
                if (const auto parserefp = VN_CAST(argp, ParseRef)) {
                    // We use an int type, this might get changed in V3Width when types resolve
                    argrefp = new AstVar{parserefp->fileline(), VVarType::BLOCKTEMP,
                                         parserefp->name(), argp->findSigned32DType()};
                    parserefp->replaceWith(argrefp);
                    VL_DO_DANGLING(parserefp->deleteTree(), parserefp);
                    // Insert argref's name into symbol table
                    m_statep->insertSym(m_curSymp, argrefp->name(), argrefp, nullptr);
                } else if (const auto largrefp = VN_CAST(argp, Var)) {
                    argrefp = largrefp;
                    // Insert argref's name into symbol table
                    m_statep->insertSym(m_curSymp, argrefp->name(), argrefp, nullptr);
                } else if (VN_IS(argp, Empty)) {
                } else {
                    argp->v3error("'foreach' loop variable expects simple variable name");
                }
            }
            iterateChildren(nodep);
        }
    }

    void visit(AstWithParse* nodep) override {
        // Change WITHPARSE(FUNCREF, equation) to FUNCREF(WITH(equation))
        const auto funcrefp = VN_AS(nodep->funcrefp(), NodeFTaskRef);
        UASSERT_OBJ(funcrefp, nodep, "'with' only can operate on a function/task");
        string name = "item";
        FileLine* argFl = nodep->fileline();
        if (const auto argp = VN_CAST(funcrefp->pinsp(), Arg)) {
            if (const auto parserefp = VN_CAST(argp->exprp(), ParseRef)) {
                name = parserefp->name();
                argFl = parserefp->fileline();
            } else {
                argp->v3error("'with' function expects simple variable name");
            }
            if (argp->nextp())
                argp->nextp()->v3error("'with' function expects only up to one argument");
            VL_DO_DANGLING(argp->unlinkFrBackWithNext()->deleteTree(), argp);
        }
        // Type depends on the method used, let V3Width figure it out later
        if (nodep->exprp()) {  // Else empty expression and pretend no "with"
            const auto indexArgRefp = new AstLambdaArgRef{argFl, name + "__DOT__index", true};
            const auto valueArgRefp = new AstLambdaArgRef{argFl, name, false};
            const auto newp = new AstWith{nodep->fileline(), indexArgRefp, valueArgRefp,
                                          nodep->exprp()->unlinkFrBackWithNext()};
            funcrefp->addPinsp(newp);
        }
        nodep->replaceWith(funcrefp->unlinkFrBack());
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstWith* nodep) override {
        // Symbol table needs nodep->name() as the index variable's name
        // Iteration will pickup the AstVar we made under AstWith
        VL_RESTORER(m_curSymp);
        {
            ++m_modWithNum;
            m_curSymp = m_statep->insertBlock(m_curSymp, "__Vwith" + cvtToStr(m_modWithNum), nodep,
                                              m_classOrPackagep);
            m_curSymp->fallbackp(VL_RESTORER_PREV(m_curSymp));
            UASSERT_OBJ(nodep->indexArgRefp(), nodep, "Missing lambda argref");
            UASSERT_OBJ(nodep->valueArgRefp(), nodep, "Missing lambda argref");
            // Insert argref's name into symbol table
            m_statep->insertSym(m_curSymp, nodep->valueArgRefp()->name(), nodep->valueArgRefp(),
                                nullptr);
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LinkDotFindVisitor(AstNetlist* rootp, LinkDotState* statep)
        : m_statep{statep} {
        UINFO(4, __FUNCTION__ << ": " << endl);

        iterate(rootp);
    }
    ~LinkDotFindVisitor() override = default;
};

//======================================================================

class LinkDotParamVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on global
    //  *::user1p()             -> See LinkDotState
    //  *::user2p()             -> See LinkDotState
    //  *::user4()              -> See LinkDotState

    // STATE
    LinkDotState* const m_statep;  // State to pass between visitors, including symbol table
    AstNodeModule* m_modp = nullptr;  // Current module

    void pinImplicitExprRecurse(AstNode* nodep) {
        // Under a pin, Check interconnect expression for a pin reference or a concat.
        // Create implicit variable as needed
        if (VN_IS(nodep, Dot)) {  // Not creating a simple implied type,
            // and implying something else would just confuse later errors
        } else if (VN_IS(nodep, VarRef) || VN_IS(nodep, ParseRef)) {
            // To prevent user errors, we should only do single bit
            // implicit vars, however some netlists (MIPS) expect single
            // bit implicit wires to get created with range 0:0 etc.
            m_statep->implicitOkAdd(m_modp, nodep->name());
        }
        // These are perhaps a little too generous, as a SELect of siga[sigb]
        // perhaps shouldn't create an implicit variable.  But, we've warned...
        else {
            if (nodep->op1p()) pinImplicitExprRecurse(nodep->op1p());
            if (nodep->op2p()) pinImplicitExprRecurse(nodep->op2p());
            if (nodep->op3p()) pinImplicitExprRecurse(nodep->op3p());
            if (nodep->op4p()) pinImplicitExprRecurse(nodep->op4p());
            if (nodep->nextp()) pinImplicitExprRecurse(nodep->nextp());
        }
    }

    // VISITs
    void visit(AstTypeTable*) override {}
    void visit(AstConstPool*) override {}
    void visit(AstNodeModule* nodep) override {
        UINFO(5, "   " << nodep << endl);
        if (nodep->dead() || !nodep->user4()) {
            UINFO(4, "Mark dead module " << nodep << endl);
            UASSERT_OBJ(m_statep->forPrearray(), nodep,
                        "Dead module persisted past where should have removed");
            // Don't remove now, because we may have a tree of
            // parameterized modules with VARXREFs into the deleted module
            // region.  V3Dead should cleanup.
            // Downstream visitors up until V3Dead need to check for nodep->dead.
            nodep->dead(true);
        } else {
            m_modp = nodep;
            iterateChildren(nodep);
            m_modp = nullptr;
        }
    }
    void visit(AstPin* nodep) override {
        // Pin: Link to submodule's port
        // Deal with implicit definitions - do before Resolve visitor as may
        // be referenced above declaration
        if (nodep->exprp()  // Else specifically unconnected pin
            && !nodep->svImplicit()) {  // SV 19.11.3: .name pins don't allow implicit decls
            pinImplicitExprRecurse(nodep->exprp());
        }
    }
    void visit(AstDefParam* nodep) override {
        iterateChildren(nodep);
        nodep->v3warn(DEFPARAM, "defparam is deprecated (IEEE 1800-2017 C.4.1)\n"
                                    << nodep->warnMore()
                                    << "... Suggest use instantiation with #(."
                                    << nodep->prettyName() << "(...etc...))");
        VSymEnt* const foundp = m_statep->getNodeSym(nodep)->findIdFallback(nodep->path());
        AstCell* const cellp = foundp ? VN_AS(foundp->nodep(), Cell) : nullptr;
        if (!cellp) {
            nodep->v3error("In defparam, instance " << nodep->path() << " never declared");
        } else {
            AstNodeExpr* const exprp = nodep->rhsp()->unlinkFrBack();
            UINFO(9, "Defparam cell " << nodep->path() << "." << nodep->name() << " attach-to "
                                      << cellp << "  <= " << exprp << endl);
            // Don't need to check the name of the defparam exists.  V3Param does.
            AstPin* const pinp = new AstPin{nodep->fileline(),
                                            -1,  // Pin# not relevant
                                            nodep->name(), exprp};
            pinp->param(true);
            cellp->addParamsp(pinp);
        }
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstPort* nodep) override {
        // Port: Stash the pin number
        // Need to set pin numbers after varnames are created
        // But before we do the final resolution based on names
        VSymEnt* const foundp = m_statep->getNodeSym(m_modp)->findIdFlat(nodep->name());
        AstVar* const refp = foundp ? VN_CAST(foundp->nodep(), Var) : nullptr;
        if (!foundp) {
            nodep->v3error(
                "Input/output/inout declaration not found for port: " << nodep->prettyNameQ());
        } else if (!refp || (!refp->isIO() && !refp->isIfaceRef())) {
            nodep->v3error("Pin is not an in/out/inout/interface: " << nodep->prettyNameQ());
        } else {
            if (refp->user4()) {
                nodep->v3error("Duplicate declaration of port: "
                               << nodep->prettyNameQ() << '\n'
                               << nodep->warnContextPrimary() << '\n'
                               << refp->warnOther() << "... Location of original declaration\n"
                               << refp->warnContextSecondary());
            }
            refp->user4(true);
            VSymEnt* const symp = m_statep->insertSym(m_statep->getNodeSym(m_modp),
                                                      "__pinNumber" + cvtToStr(nodep->pinNum()),
                                                      refp, nullptr /*classOrPackagep*/);
            symp->exported(false);
            refp->pinNum(nodep->pinNum());
            // Put the variable where the port is, so that variables stay
            // in pin number sorted order. Otherwise hierarchical or XML
            // may botch by-position instances.
            nodep->addHereThisAsNext(refp->unlinkFrBack());
        }
        // Ports not needed any more
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstAssignW* nodep) override {
        // Deal with implicit definitions
        // We used to nodep->allowImplicit() here, but it turns out
        // normal "assigns" can also make implicit wires.  Yuk.
        pinImplicitExprRecurse(nodep->lhsp());
        iterateChildren(nodep);
    }
    void visit(AstAssignAlias* nodep) override {
        // tran gates need implicit creation
        // As VarRefs don't exist in forPrimary, sanity check
        UASSERT_OBJ(!m_statep->forPrimary(), nodep, "Assign aliases unexpected pre-dot");
        if (AstVarRef* const forrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            pinImplicitExprRecurse(forrefp);
        }
        if (AstVarRef* const forrefp = VN_CAST(nodep->rhsp(), VarRef)) {
            pinImplicitExprRecurse(forrefp);
        }
        iterateChildren(nodep);
    }
    void visit(AstImplicit* nodep) override {
        // Unsupported gates need implicit creation
        pinImplicitExprRecurse(nodep->exprsp());
        // We're done with implicit gates
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        if (auto* const fwdp = VN_CAST(nodep->classOrPackageNodep(), TypedefFwd)) {
            // Relink forward definitions to the "real" definition
            VSymEnt* const foundp = m_statep->getNodeSym(fwdp)->findIdFallback(fwdp->name());
            if (foundp && (VN_IS(foundp->nodep(), Class) || VN_IS(foundp->nodep(), Package))) {
                nodep->classOrPackagep(VN_AS(foundp->nodep(), NodeModule));
            } else if (foundp && VN_IS(foundp->nodep(), ParamTypeDType)) {
                UASSERT(m_statep->forPrimary(), "Param types should have been resolved");
                nodep->classOrPackageNodep(VN_AS(foundp->nodep(), ParamTypeDType));
            } else {
                if (foundp) UINFO(1, "found nodep = " << foundp->nodep() << endl);
                nodep->v3error(
                    "Forward typedef used as class/package does not resolve to class/package: "
                    << nodep->prettyNameQ() << '\n'
                    << nodep->warnContextPrimary() << '\n'
                    << (foundp ? nodep->warnMore() + "... Object with matching name\n"
                                     + foundp->nodep()->warnContextSecondary()
                               : ""));
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstPull* nodep) override {
        // Deal with implicit definitions
        // We used to nodep->allowImplicit() here, but it turns out
        // normal "assigns" can also make implicit wires.  Yuk.
        pinImplicitExprRecurse(nodep->lhsp());
        iterateChildren(nodep);
    }
    void visit(AstTypedefFwd* nodep) override {
        VSymEnt* const foundp = m_statep->getNodeSym(nodep)->findIdFallback(nodep->name());
        if (!foundp && v3Global.opt.pedantic()
            && nodep->name() != "process") {  // Process is dangling as isn't implemented yet
            // We only check it was ever really defined in pedantic mode, as it
            // might have been in a header file referring to a module we never
            // needed so there are false positives
            nodep->v3error(
                "Forward typedef unused or does not resolve to a data type (IEEE 1800-2017 6.18): "
                << nodep->prettyNameQ());
        }
        // We only needed the forward declaration in order to parse correctly.
        // Delete later as may be ClassOrPackageRef's still pointing to it
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LinkDotParamVisitor(AstNetlist* rootp, LinkDotState* statep)
        : m_statep{statep} {
        UINFO(4, __FUNCTION__ << ": " << endl);
        iterate(rootp);
    }
    ~LinkDotParamVisitor() override = default;
};

//======================================================================

class LinkDotScopeVisitor final : public VNVisitor {

    // STATE
    LinkDotState* const m_statep;  // State to pass between visitors, including symbol table
    const AstScope* m_scopep = nullptr;  // The current scope
    VSymEnt* m_modSymp = nullptr;  // Symbol entry for current module

    // VISITs
    void visit(AstNetlist* nodep) override {
        // Recurse..., backward as must do packages before using packages
        iterateChildrenBackwardsConst(nodep);
    }
    void visit(AstConstPool*) override {}
    void visit(AstScope* nodep) override {
        UINFO(8, "  SCOPE " << nodep << endl);
        UASSERT_OBJ(m_statep->forScopeCreation(), nodep,
                    "Scopes should only exist right after V3Scope");
        // Using the CELL names, we created all hierarchy.  We now need to match this Scope
        // up with the hierarchy created by the CELL names.
        m_modSymp = m_statep->getScopeSym(nodep);
        m_scopep = nodep;
        iterateChildren(nodep);
        m_modSymp = nullptr;
        m_scopep = nullptr;
    }
    void visit(AstVarScope* nodep) override {
        if (!nodep->varp()->isFuncLocal() && !nodep->varp()->isClassMember()) {
            VSymEnt* const varSymp
                = m_statep->insertSym(m_modSymp, nodep->varp()->name(), nodep, nullptr);
            if (nodep->varp()->isIfaceRef() && nodep->varp()->isIfaceParent()) {
                UINFO(9, "Iface parent ref var " << nodep->varp()->name() << " " << nodep << endl);
                // Find the interface cell the var references
                AstIfaceRefDType* const dtypep
                    = LinkDotState::ifaceRefFromArray(nodep->varp()->dtypep());
                UASSERT_OBJ(dtypep, nodep, "Non AstIfaceRefDType on isIfaceRef() var");
                UINFO(9, "Iface parent dtype " << dtypep << endl);
                const string ifcellname = dtypep->cellName();
                string baddot;
                VSymEnt* okSymp;
                VSymEnt* cellSymp = m_statep->findDotted(nodep->fileline(), m_modSymp, ifcellname,
                                                         baddot, okSymp);
                UASSERT_OBJ(
                    cellSymp, nodep,
                    "No symbol for interface instance: " << nodep->prettyNameQ(ifcellname));
                UINFO(5, "       Found interface instance: se" << cvtToHex(cellSymp) << " "
                                                               << cellSymp->nodep() << endl);
                if (dtypep->modportName() != "") {
                    VSymEnt* const mpSymp = m_statep->findDotted(nodep->fileline(), m_modSymp,
                                                                 ifcellname, baddot, okSymp);
                    UASSERT_OBJ(mpSymp, nodep,
                                "No symbol for interface modport: "
                                    << nodep->prettyNameQ(dtypep->modportName()));
                    cellSymp = mpSymp;
                    UINFO(5, "       Found modport cell: se" << cvtToHex(cellSymp) << " "
                                                             << mpSymp->nodep() << endl);
                }
                // Interface reference; need to put whole thing into
                // symtable, but can't clone it now as we may have a later
                // alias for it.
                m_statep->insertScopeAlias(LinkDotState::SAMN_IFTOP, varSymp, cellSymp);
            }
        }
    }
    void visit(AstNodeFTask* nodep) override {
        VSymEnt* const symp = m_statep->insertBlock(m_modSymp, nodep->name(), nodep, nullptr);
        symp->fallbackp(m_modSymp);
        iterateChildren(nodep);
    }
    void visit(AstNodeForeach* nodep) override {
        VSymEnt* const symp = m_statep->insertBlock(m_modSymp, nodep->name(), nodep, nullptr);
        symp->fallbackp(m_modSymp);
        // No recursion, we don't want to pick up variables
    }
    void visit(AstWith* nodep) override {
        VSymEnt* const symp = m_statep->insertBlock(m_modSymp, nodep->name(), nodep, nullptr);
        symp->fallbackp(m_modSymp);
        // No recursion, we don't want to pick up variables
    }
    void visit(AstAssignAlias* nodep) override {
        // Track aliases created by V3Inline; if we get a VARXREF(aliased_from)
        // we'll need to replace it with a VARXREF(aliased_to)
        if (debug() >= 9) nodep->dumpTree("-    alias: ");
        AstVarScope* const fromVscp = VN_AS(nodep->lhsp(), VarRef)->varScopep();
        AstVarScope* const toVscp = VN_AS(nodep->rhsp(), VarRef)->varScopep();
        UASSERT_OBJ(fromVscp && toVscp, nodep, "Bad alias scopes");
        fromVscp->user2p(toVscp);
        iterateChildren(nodep);
    }
    void visit(AstAssignVarScope* nodep) override {
        UINFO(5, "ASSIGNVARSCOPE  " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree("-    avs: ");
        VSymEnt* rhsSymp;
        {
            AstVarRef* const refp = VN_CAST(nodep->rhsp(), VarRef);
            AstVarXRef* const xrefp = VN_CAST(nodep->rhsp(), VarXRef);
            UASSERT_OBJ(refp || xrefp, nodep,
                        "Unsupported: Non Var(X)Ref attached to interface pin");
            string inl
                = ((xrefp && xrefp->inlinedDots().size()) ? (xrefp->inlinedDots() + "__DOT__")
                                                          : "");
            VSymEnt* symp = nullptr;
            string scopename;
            while (!symp) {
                scopename
                    = refp ? refp->name() : (inl.size() ? (inl + xrefp->name()) : xrefp->name());
                string baddot;
                VSymEnt* okSymp;
                symp = m_statep->findDotted(nodep->rhsp()->fileline(), m_modSymp, scopename,
                                            baddot, okSymp);
                if (inl == "") break;
                inl = LinkDotState::removeLastInlineScope(inl);
            }
            if (!symp) {
                UINFO(9, "No symbol for interface alias rhs ("
                             << std::string{refp ? "VARREF " : "VARXREF "} << scopename << ")"
                             << endl);
            }
            UASSERT_OBJ(symp, nodep, "No symbol for interface alias rhs");
            UINFO(5, "       Found a linked scope RHS: " << scopename << "  se" << cvtToHex(symp)
                                                         << " " << symp->nodep() << endl);
            rhsSymp = symp;
        }
        VSymEnt* lhsSymp;
        {
            const AstVarXRef* const xrefp = VN_CAST(nodep->lhsp(), VarXRef);
            const AstVarRef* const refp = VN_CAST(nodep->lhsp(), VarRef);

            UASSERT_OBJ(refp || xrefp, nodep,
                        "Unsupported: Non Var(X)Ref attached to interface pin");
            const string scopename
                = refp ? refp->varp()->name() : xrefp->dotted() + "." + xrefp->name();
            string baddot;
            VSymEnt* okSymp;
            VSymEnt* const symp = m_statep->findDotted(nodep->lhsp()->fileline(), m_modSymp,
                                                       scopename, baddot, okSymp);
            UASSERT_OBJ(symp, nodep, "No symbol for interface alias lhs");
            UINFO(5, "       Found a linked scope LHS: " << scopename << "  se" << cvtToHex(symp)
                                                         << " " << symp->nodep() << endl);
            lhsSymp = symp;
        }
        // Remember the alias - can't do it yet because we may have additional symbols to be added,
        // or maybe an alias of an alias
        m_statep->insertScopeAlias(LinkDotState::SAMN_IFTOP, lhsSymp, rhsSymp);
        // We have stored the link, we don't need these any more
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    // For speed, don't recurse things that can't have scope
    // Note we allow AstNodeStmt's as generates may be under them
    void visit(AstCell*) override {}
    void visit(AstVar*) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LinkDotScopeVisitor(AstNetlist* rootp, LinkDotState* statep)
        : m_statep{statep} {
        UINFO(4, __FUNCTION__ << ": " << endl);
        iterate(rootp);
    }
    ~LinkDotScopeVisitor() override = default;
};

//======================================================================

// Iterate an interface to resolve modports
class LinkDotIfaceVisitor final : public VNVisitor {
    // STATE
    LinkDotState* const m_statep;  // State to pass between visitors, including symbol table
    VSymEnt* m_curSymp;  // Symbol Entry for current table, where to lookup/insert

    // VISITs
    void visit(AstModport* nodep) override {
        // Modport: Remember its name for later resolution
        UINFO(5, "   fiv: " << nodep << endl);
        VL_RESTORER(m_curSymp);
        {
            // Create symbol table for the vars
            m_curSymp = m_statep->insertBlock(m_curSymp, nodep->name(), nodep, nullptr);
            m_curSymp->fallbackp(VL_RESTORER_PREV(m_curSymp));
            iterateChildren(nodep);
        }
    }
    void visit(AstModportFTaskRef* nodep) override {
        UINFO(5, "   fif: " << nodep << endl);
        iterateChildren(nodep);
        if (nodep->isExport()) nodep->v3warn(E_UNSUPPORTED, "Unsupported: modport export");
        VSymEnt* const symp = m_curSymp->findIdFallback(nodep->name());
        if (!symp) {
            nodep->v3error("Modport item not found: " << nodep->prettyNameQ());
        } else if (AstNodeFTask* const ftaskp = VN_CAST(symp->nodep(), NodeFTask)) {
            // Make symbol under modport that points at the _interface_'s var, not the modport.
            nodep->ftaskp(ftaskp);
            VSymEnt* const subSymp
                = m_statep->insertSym(m_curSymp, nodep->name(), ftaskp, nullptr /*package*/);
            m_statep->insertScopeAlias(LinkDotState::SAMN_MODPORT, subSymp, symp);
        } else {
            nodep->v3error("Modport item is not a function/task: " << nodep->prettyNameQ());
        }
        if (m_statep->forScopeCreation()) {
            // Done with AstModportFTaskRef.
            // Delete to prevent problems if we dead-delete pointed to ftask
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstModportVarRef* nodep) override {
        UINFO(5, "   fiv: " << nodep << endl);
        iterateChildren(nodep);
        VSymEnt* const symp = m_curSymp->findIdFallback(nodep->name());
        if (!symp) {
            nodep->v3error("Modport item not found: " << nodep->prettyNameQ());
        } else if (AstVar* const varp = VN_CAST(symp->nodep(), Var)) {
            // Make symbol under modport that points at the _interface_'s var via the modport.
            // (Need modport still to test input/output markings)
            nodep->varp(varp);
            m_statep->insertSym(m_curSymp, nodep->name(), nodep, nullptr /*package*/);
        } else if (AstVarScope* const vscp = VN_CAST(symp->nodep(), VarScope)) {
            // Make symbol under modport that points at the _interface_'s var, not the modport.
            nodep->varp(vscp->varp());
            m_statep->insertSym(m_curSymp, nodep->name(), vscp, nullptr /*package*/);
        } else {
            nodep->v3error("Modport item is not a variable: " << nodep->prettyNameQ());
        }
        if (m_statep->forScopeCreation()) {
            // Done with AstModportVarRef.
            // Delete to prevent problems if we dead-delete pointed to variable
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LinkDotIfaceVisitor(AstIface* nodep, VSymEnt* curSymp, LinkDotState* statep)
        : m_statep{statep}
        , m_curSymp{curSymp} {
        UINFO(4, __FUNCTION__ << ": " << endl);
        iterate(nodep);
    }
    ~LinkDotIfaceVisitor() override = default;
};

void LinkDotState::computeIfaceModSyms() {
    for (const auto& itr : m_ifaceModSyms) {
        AstIface* const nodep = itr.first;
        VSymEnt* const symp = itr.second;
        LinkDotIfaceVisitor{nodep, symp, this};
    }
    m_ifaceModSyms.clear();
}

//======================================================================

class LinkDotResolveVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on global
    //  *::user1p()             -> See LinkDotState
    //  *::user2p()             -> See LinkDotState
    //  *::user3()              // bool. Processed
    //  *::user4()              -> See LinkDotState
    const VNUser3InUse m_inuser3;

    // TYPES
    enum DotPosition : uint8_t {
        DP_NONE = 0,  // Not under a DOT
        DP_PACKAGE,  // {package}:: DOT
        DP_SCOPE,  // [DOT...] {scope-or-var} DOT
        DP_FINAL,  // [DOT...] {var-or-func-or-dtype} with no following dots
        DP_MEMBER
    };  // DOT {member-name} [DOT...]

    // STATE
    LinkDotState* const m_statep;  // State, including dotted symbol table
    VSymEnt* m_curSymp = nullptr;  // SymEnt for current lookup point
    VSymEnt* m_modSymp = nullptr;  // SymEnt for current module
    VSymEnt* m_pinSymp = nullptr;  // SymEnt for pin lookups
    const AstCell* m_cellp = nullptr;  // Current cell
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    int m_modportNum = 0;  // Uniqueify modport numbers
    bool m_inSens = false;  // True if in senitem
    std::set<std::string> m_ifClassImpNames;  // Names imported from interface class
    std::set<AstClass*> m_extendsParam;  // Classes that have a parameterized super class
                                         // (except the default instances)
                                         // They are added to the set only in linkDotPrimary.
    bool m_insideClassExtParam = false;  // Inside a class from m_extendsParam
    bool m_explicitSuperNew = false;  // Hit a "super.new" call inside a "new" function
    std::map<AstNode*, AstPin*> m_usedPins;  // Pin used in this cell, map to duplicate

    struct DotStates {
        DotPosition m_dotPos;  // Scope part of dotted resolution
        VSymEnt* m_dotSymp;  // SymEnt for dotted AstParse lookup
        const AstDot* m_dotp;  // Current dot
        bool m_super;  // Starts with super reference
        bool m_unresolvedCell;  // Unresolved cell, needs help from V3Param
        bool m_unresolvedClass;  // Unresolved class reference, needs help from V3Param
        AstNode* m_unlinkedScopep;  // Unresolved scope, needs corresponding VarXRef
        bool m_dotErr;  // Error found in dotted resolution, ignore upwards
        string m_dotText;  // String of dotted names found in below parseref
        DotStates() { init(nullptr); }
        ~DotStates() = default;
        void init(VSymEnt* curSymp) {
            m_dotPos = DP_NONE;
            m_dotSymp = curSymp;
            m_dotp = nullptr;
            m_super = false;
            m_dotErr = false;
            m_dotText = "";
            m_unresolvedCell = false;
            m_unresolvedClass = false;
            m_unlinkedScopep = nullptr;
        }
        string ascii() const {
            static const char* const names[] = {"NONE", "PACKAGE", "SCOPE", "FINAL", "MEMBER"};
            std::ostringstream sstr;
            sstr << "ds=" << names[m_dotPos];
            sstr << "  dse" << cvtToHex(m_dotSymp);
            sstr << "  sup=" << m_super;
            sstr << "  txt=" << m_dotText;
            sstr << "  unrCell=" << m_unresolvedCell;
            sstr << "  unrClass=" << m_unresolvedClass;
            return sstr.str();
        }
    } m_ds;  // State to preserve across recursions

    // METHODS - Variables
    AstVar* createImplicitVar(VSymEnt* /*lookupSymp*/, AstParseRef* nodep, AstNodeModule* modp,
                              VSymEnt* moduleSymp, bool noWarn) {
        // Create implicit after warning
        if (!noWarn) {
            if (nodep->fileline()->warnIsOff(V3ErrorCode::I_DEF_NETTYPE_WIRE)) {
                const string suggest = m_statep->suggestSymFallback(moduleSymp, nodep->name(),
                                                                    LinkNodeMatcherVar{});
                nodep->v3error("Signal definition not found, and implicit disabled with "
                               "`default_nettype: "
                               << nodep->prettyNameQ() << '\n'
                               << (suggest.empty() ? "" : nodep->warnMore() + suggest));

            }
            // Bypass looking for suggestions if IMPLICIT is turned off
            // as there could be thousands of these suppressed in large netlists
            else if (!nodep->fileline()->warnIsOff(V3ErrorCode::IMPLICIT)) {
                const string suggest = m_statep->suggestSymFallback(moduleSymp, nodep->name(),
                                                                    LinkNodeMatcherVar{});
                nodep->v3warn(IMPLICIT,
                              "Signal definition not found, creating implicitly: "
                                  << nodep->prettyNameQ() << '\n'
                                  << (suggest.empty() ? "" : nodep->warnMore() + suggest));
            }
        }
        AstVar* const newp
            = new AstVar{nodep->fileline(), VVarType::WIRE, nodep->name(), VFlagLogicPacked{}, 1};
        newp->trace(modp->modTrace());
        modp->addStmtsp(newp);
        // Link it to signal list, must add the variable under the module;
        // current scope might be lower now
        m_statep->insertSym(moduleSymp, newp->name(), newp, nullptr /*classOrPackagep*/);
        return newp;
    }
    AstVar* foundToVarp(const VSymEnt* symp, AstNode* nodep, VAccess access) {
        // Return a variable if possible, auto converting a modport to variable
        if (!symp) {
            return nullptr;
        } else if (VN_IS(symp->nodep(), Var)) {
            return VN_AS(symp->nodep(), Var);
        } else if (VN_IS(symp->nodep(), ModportVarRef)) {
            AstModportVarRef* const snodep = VN_AS(symp->nodep(), ModportVarRef);
            AstVar* const varp = snodep->varp();
            if (access.isWriteOrRW() && snodep->direction().isReadOnly()) {
                nodep->v3error("Attempt to drive input-only modport: " << nodep->prettyNameQ());
            }  // else other simulators don't warn about reading, and IEEE doesn't say illegal
            return varp;
        } else {
            return nullptr;
        }
    }
    AstNodeStmt* addImplicitSuperNewCall(AstFunc* nodep) {
        // Returns the added node
        FileLine* const fl = nodep->fileline();
        AstDot* const superNewp
            = new AstDot{fl, false, new AstParseRef{fl, VParseRefExp::PX_ROOT, "super"},
                         new AstNew{fl, nullptr}};
        AstNodeStmt* const superNewStmtp = superNewp->makeStmt();
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            // super.new shall be the first statement (IEEE 1800-2017 8.15)
            // but some nodes (such as variable declarations and typedefs) should stay before
            if (VN_IS(stmtp, NodeStmt)) {
                stmtp->addHereThisAsNext(superNewStmtp);
                return superNewStmtp;
            }
        }
        // There were no statements
        nodep->addStmtsp(superNewStmtp);
        return superNewStmtp;
    }
    void taskFuncSwapCheck(AstNodeFTaskRef* nodep) {
        if (nodep->taskp() && VN_IS(nodep->taskp(), Task) && VN_IS(nodep, FuncRef)) {
            nodep->v3error("Illegal call of a task as a function: " << nodep->prettyNameQ());
        }
    }
    void checkNoDot(AstNode* nodep) {
        if (VL_UNLIKELY(m_ds.m_dotPos != DP_NONE)) {
            // UINFO(9, "ds=" << m_ds.ascii() << endl);
            nodep->v3error("Syntax error: Not expecting " << nodep->type() << " under a "
                                                          << nodep->backp()->type()
                                                          << " in dotted expression");
            m_ds.m_dotErr = true;
        }
    }
    AstVar* findIfaceTopVarp(AstNode* nodep, VSymEnt* parentEntp, const string& name) {
        const string findName = name + "__Viftop";
        VSymEnt* const ifaceSymp = parentEntp->findIdFallback(findName);
        AstVar* const ifaceTopVarp = ifaceSymp ? VN_AS(ifaceSymp->nodep(), Var) : nullptr;
        UASSERT_OBJ(ifaceTopVarp, nodep, "Can't find interface var ref: " << findName);
        return ifaceTopVarp;
    }
    void markAndCheckPinDup(AstPin* nodep, AstNode* refp, const char* whatp) {
        const auto pair = m_usedPins.emplace(refp, nodep);
        if (!pair.second) {
            AstNode* const origp = pair.first->second;
            nodep->v3error("Duplicate " << whatp << " connection: " << nodep->prettyNameQ() << '\n'
                                        << nodep->warnContextPrimary() << '\n'
                                        << origp->warnOther() << "... Location of original "
                                        << whatp << " connection\n"
                                        << origp->warnContextSecondary());
        }
    }
    VSymEnt* getCreateClockingEventSymEnt(AstClocking* clockingp) {
        if (!clockingp->eventp()) {
            AstVar* const eventp = new AstVar{
                clockingp->fileline(), VVarType::MODULETEMP, clockingp->name(), VFlagChildDType{},
                new AstBasicDType{clockingp->fileline(), VBasicDTypeKwd::EVENT}};
            clockingp->eventp(eventp);
            // Trigger the clocking event in Observed (IEEE 1800-2017 14.13)
            clockingp->addNextHere(new AstAlwaysObserved{
                clockingp->fileline(),
                new AstSenTree{clockingp->fileline(), clockingp->sensesp()->cloneTree(false)},
                new AstFireEvent{clockingp->fileline(),
                                 new AstVarRef{clockingp->fileline(), eventp, VAccess::WRITE},
                                 false}});
            v3Global.setHasEvents();
            eventp->user1p(new VSymEnt{m_statep->symsp(), eventp});
        }
        return reinterpret_cast<VSymEnt*>(clockingp->eventp()->user1p());
    }

    bool isParamedClassRef(const AstNode* nodep) {
        // Is this a parameterized reference to a class, or a reference to class parameter
        if (const auto* classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            if (classRefp->paramsp()) return true;
            const auto* classp = classRefp->classOrPackageNodep();
            while (const auto* typedefp = VN_CAST(classp, Typedef)) classp = typedefp->subDTypep();
            return (VN_IS(classp, ClassRefDType) && VN_AS(classp, ClassRefDType)->paramsp())
                   || VN_IS(classp, ParamTypeDType);
        }
        return false;
    }
    VSymEnt* getThisClassSymp() {
        VSymEnt* classSymp = m_ds.m_dotSymp;
        do {
            classSymp = classSymp->parentp();
        } while (classSymp && !VN_IS(classSymp->nodep(), Class));
        return classSymp;
    }
    void importImplementsClass(AstClass* implementsClassp, VSymEnt* interfaceSymp,
                               AstClass* interfaceClassp) {
        UINFO(8, "importImplementsClass to " << implementsClassp << " from " << interfaceClassp
                                             << endl);
        for (VSymEnt::const_iterator it = interfaceSymp->begin(); it != interfaceSymp->end();
             ++it) {
            if (AstNode* interfaceSubp = it->second->nodep()) {
                UINFO(8, "  SymFunc " << interfaceSubp << endl);
                if (VN_IS(interfaceSubp, NodeFTask)) {
                    const VSymEnt* const foundp = m_curSymp->findIdFlat(interfaceSubp->name());
                    bool existsInChild = foundp && !foundp->imported();
                    if (!existsInChild && !implementsClassp->isInterfaceClass()) {
                        implementsClassp->v3error(
                            "Class " << implementsClassp->prettyNameQ() << " implements "
                                     << interfaceClassp->prettyNameQ()
                                     << " but is missing implementation for "
                                     << interfaceSubp->prettyNameQ() << " (IEEE 1800-2017 8.26)\n"
                                     << implementsClassp->warnContextPrimary() << '\n'
                                     << interfaceSubp->warnOther()
                                     << "... Location of interface class's function\n"
                                     << interfaceSubp->warnContextSecondary());
                    }
                    if (!existsInChild
                        && m_ifClassImpNames.find(interfaceSubp->name())
                               != m_ifClassImpNames.end()) {
                        implementsClassp->v3error(
                            "Class " << implementsClassp->prettyNameQ() << " implements "
                                     << interfaceClassp->prettyNameQ()
                                     << " but missing inheritance conflict resolution for "
                                     << interfaceSubp->prettyNameQ()
                                     << " (IEEE 1800-2017 8.26.6.2)\n"
                                     << implementsClassp->warnContextPrimary() << '\n'
                                     << interfaceSubp->warnOther()
                                     << "... Location of interface class's function\n"
                                     << interfaceSubp->warnContextSecondary());
                    }
                    m_ifClassImpNames.emplace(interfaceSubp->name());
                }
            }
        }
    }
    void importSymbolsFromExtended(AstClass* const nodep, AstClassExtends* const cextp) {
        AstClass* const baseClassp = cextp->classp();
        VSymEnt* const srcp = m_statep->getNodeSym(baseClassp);
        if (baseClassp->isInterfaceClass()) importImplementsClass(nodep, srcp, baseClassp);
        if (!cextp->isImplements()) m_curSymp->importFromClass(m_statep->symsp(), srcp);
    }
    void classExtendImport(AstClass* nodep) {
        // A class reference might be to a class that is later in Ast due to
        // e.g. parmaeterization or referring to a "class (type T) extends T"
        // Resolve it so later Class:: references into its base classes work
        VL_RESTORER(m_ds);
        VSymEnt* const srcp = m_statep->getNodeSym(nodep);
        m_ds.init(srcp);
        iterate(nodep);
    }
    void updateVarUse(AstVar* nodep) {
        // Avoid dotted.PARAM false positive when in a parameter block
        // that is if ()'ed off by same dotted name as another block
        if (nodep && nodep->isParam()) nodep->usedParam(true);
    }

    // VISITs
    void visit(AstNetlist* nodep) override {
        // Recurse..., backward as must do packages before using packages
        iterateChildrenBackwardsConst(nodep);
    }
    void visit(AstTypeTable*) override {}
    void visit(AstConstPool*) override {}
    void visit(AstNodeModule* nodep) override {
        if (nodep->dead()) return;
        checkNoDot(nodep);
        UINFO(8, "  " << nodep << endl);
        m_ds.init(m_curSymp);
        m_ds.m_dotSymp = m_curSymp = m_modSymp
            = m_statep->getNodeSym(nodep);  // Until overridden by a SCOPE
        m_cellp = nullptr;
        m_modp = nodep;
        m_modportNum = 0;
        iterateChildren(nodep);
        m_modp = nullptr;
        m_ds.m_dotSymp = m_curSymp = m_modSymp = nullptr;
    }
    void visit(AstScope* nodep) override {
        UINFO(8, "   " << nodep << endl);
        VL_RESTORER(m_modSymp);
        VL_RESTORER(m_curSymp);
        {
            checkNoDot(nodep);
            m_ds.m_dotSymp = m_curSymp = m_modSymp = m_statep->getScopeSym(nodep);
            iterateChildren(nodep);
            m_ds.m_dotSymp = m_curSymp = m_modSymp = nullptr;
        }
    }
    void visit(AstCellInline* nodep) override {
        checkNoDot(nodep);
        if (m_statep->forScopeCreation() && !v3Global.opt.vpi()) {
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstCell* nodep) override {
        // Cell: Recurse inside or cleanup not founds
        checkNoDot(nodep);
        m_usedPins.clear();
        UASSERT_OBJ(nodep->modp(), nodep,
                    "Cell has unlinked module");  // V3LinkCell should have errored out
        VL_RESTORER(m_cellp);
        VL_RESTORER(m_pinSymp);
        {
            m_cellp = nodep;
            if (VN_IS(nodep->modp(), NotFoundModule)) {
                // Prevent warnings about missing pin connects
                if (nodep->pinsp()) nodep->pinsp()->unlinkFrBackWithNext()->deleteTree();
                if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
            }
            // Need to pass the module info to this cell, so we can link up the pin names
            // However can't use m_curSymp as pin connections need to use the
            // instantiator's symbols
            else {
                m_pinSymp = m_statep->getNodeSym(nodep->modp());
                UINFO(4, "(Backto) Link Cell: " << nodep << endl);
                // if (debug()) nodep->dumpTree("-  linkcell: ");
                // if (debug()) nodep->modp()->dumpTree("-  linkcemd: ");
                iterateChildren(nodep);
            }
        }
        // Parent module inherits child's publicity
        // This is done bottom up in the LinkBotupVisitor stage
    }
    void visit(AstClassRefDType* nodep) override {
        // Cell: Recurse inside or cleanup not founds
        checkNoDot(nodep);
        m_usedPins.clear();
        UASSERT_OBJ(nodep->classp(), nodep, "ClassRef has unlinked class");
        UASSERT_OBJ(m_statep->forPrimary() || !nodep->paramsp(), nodep,
                    "class reference parameter not removed by V3Param");
        VL_RESTORER(m_pinSymp);
        {
            // ClassRef's have pins, so track
            m_pinSymp = m_statep->getNodeSym(nodep->classp());
            UINFO(4, "(Backto) Link ClassRefDType: " << nodep << endl);
            // if (debug()) nodep->dumpTree("-  linkcell: ");
            // if (debug()) nodep->modp()->dumpTree("-  linkcemd: ");
            iterateChildren(nodep);
        }
    }
    void visit(AstPin* nodep) override {
        // Pin: Link to submodule's port
        checkNoDot(nodep);
        iterateChildren(nodep);
        if (!nodep->modVarp()) {
            UASSERT_OBJ(m_pinSymp, nodep, "Pin not under instance?");
            VSymEnt* const foundp = m_pinSymp->findIdFlat(nodep->name());
            const char* const whatp = nodep->param() ? "parameter" : "pin";
            if (!foundp) {
                if (nodep->name() == "__paramNumber1" && m_cellp
                    && VN_IS(m_cellp->modp(), Primitive)) {
                    // Primitive parameter is really a delay we can just ignore
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                    return;
                } else {
                    const string suggest
                        = (nodep->param() ? m_statep->suggestSymFlat(m_pinSymp, nodep->name(),
                                                                     LinkNodeMatcherVarParam{})
                                          : m_statep->suggestSymFlat(m_pinSymp, nodep->name(),
                                                                     LinkNodeMatcherVarIO{}));
                    nodep->v3warn(PINNOTFOUND,
                                  ucfirst(whatp)
                                      << " not found: " << nodep->prettyNameQ() << '\n'
                                      << (suggest.empty() ? "" : nodep->warnMore() + suggest));
                    return;
                }
            }
            VVarType refVarType = VVarType::UNKNOWN;
            bool wrongPinType = false;
            if (AstVar* const varp = VN_CAST(foundp->nodep(), Var)) {
                if (varp->isIO() || varp->isParam() || varp->isIfaceRef()) {
                    refVarType = varp->varType();
                    nodep->modVarp(varp);
                } else {
                    wrongPinType = true;
                }
            } else if (AstParamTypeDType* const typep = VN_CAST(foundp->nodep(), ParamTypeDType)) {
                refVarType = typep->varType();
                nodep->modPTypep(typep);
            } else {
                wrongPinType = true;
            }
            // Don't connect parameter pin to module ports or vice versa
            if (nodep->param() != (refVarType == VVarType::GPARAM)) wrongPinType = true;
            if (wrongPinType) {
                string targetType = LinkDotState::nodeTextType(foundp->nodep());
                targetType = VString::aOrAn(targetType) + ' ' + targetType;
                if (nodep->param()) {
                    nodep->v3error("Instance attempts to override "
                                   << nodep->prettyNameQ() << " as a " << whatp << ", but it is "
                                   << targetType);
                } else {
                    nodep->v3error("Instance attempts to connect to "
                                   << nodep->prettyNameQ() << ", but it is " << targetType);
                }
                return;
            }
            markAndCheckPinDup(nodep, foundp->nodep(), whatp);
        }
        // Early return() above when deleted
    }
    void visit(AstDot* nodep) override {
        // Legal under a DOT: AstDot, AstParseRef, AstPackageRef, AstNodeSel
        //    also a DOT can be part of an expression, but only above plus
        //    AstFTaskRef are legal children
        // Dot(PackageRef, ParseRef(text))
        // Dot(Dot(ClassOrPackageRef,ClassOrPackageRef), ParseRef(text))
        // Dot(Dot(Dot(ParseRef(text), ...
        if (nodep->user3SetOnce()) return;
        UINFO(8, "     " << nodep << endl);
        const DotStates lastStates = m_ds;
        const bool start = (m_ds.m_dotPos == DP_NONE);  // Save, as m_dotp will be changed
        {
            if (start) {  // Starting dot sequence
                if (debug() >= 9) nodep->dumpTree("-  dot-in: ");
                m_ds.init(m_curSymp);  // Start from current point
            }
            m_ds.m_dotp = nodep;  // Always, not just at start
            m_ds.m_dotPos = DP_SCOPE;

            if (VN_IS(nodep->lhsp(), ParseRef) && nodep->lhsp()->name() == "this") {
                VSymEnt* classSymp = getThisClassSymp();
                if (!classSymp) {
                    nodep->v3error("'this' used outside class (IEEE 1800-2017 8.11)");
                    m_ds.m_dotErr = true;
                } else {
                    m_ds.m_dotSymp = classSymp;
                    UINFO(8, "     this. " << m_ds.ascii() << endl);
                }
            } else if (VN_IS(nodep->lhsp(), ParseRef) && nodep->lhsp()->name() == "super") {
                const VSymEnt* classSymp = getThisClassSymp();
                if (!classSymp) {
                    nodep->v3error("'super' used outside class (IEEE 1800-2017 8.15)");
                    m_ds.m_dotErr = true;
                } else {
                    const auto classp = VN_AS(classSymp->nodep(), Class);
                    const auto cextp = classp->extendsp();
                    if (!cextp) {
                        nodep->v3error("'super' used on non-extended class (IEEE 1800-2017 8.15)");
                        m_ds.m_dotErr = true;
                    } else {
                        if (m_statep->forPrimary()
                            && m_extendsParam.find(classp) != m_extendsParam.end()) {
                            m_ds.m_unresolvedClass = true;
                        } else {
                            const auto baseClassp = cextp->classp();
                            UASSERT_OBJ(baseClassp, nodep, "Bad superclass");
                            m_ds.m_dotSymp = m_statep->getNodeSym(baseClassp);
                            m_ds.m_super = true;
                            UINFO(8, "     super. " << m_ds.ascii() << endl);
                        }
                    }
                }
            } else if (VN_IS(nodep->lhsp(), ClassOrPackageRef)) {
                // m_ds.m_dotText communicates the cell prefix between stages
                // if (!start) { nodep->lhsp()->v3error("Package reference may not be embedded in
                // dotted reference"); m_ds.m_dotErr=true; }
                m_ds.m_dotPos = DP_PACKAGE;
                iterateAndNextNull(nodep->lhsp());
            } else {
                m_ds.m_dotPos = DP_SCOPE;
                iterateAndNextNull(nodep->lhsp());
                // if (debug() >= 9) nodep->dumpTree("-  dot-lho: ");
            }
            if (m_statep->forPrimary() && isParamedClassRef(nodep->lhsp())) {
                // Dots of paramed classes will be linked after deparameterization
                m_ds.m_unresolvedClass = true;
            }
            if (m_ds.m_unresolvedCell
                && (VN_IS(nodep->lhsp(), CellRef) || VN_IS(nodep->lhsp(), CellArrayRef))) {
                m_ds.m_unlinkedScopep = nodep->lhsp();
            }
            if (!m_ds.m_dotErr) {  // Once something wrong, give up
                // Top 'final' dot RHS is final RHS, else it's a
                // DOT(DOT(x,*here*),real-rhs) which we consider a RHS
                if (start && m_ds.m_dotPos == DP_SCOPE) m_ds.m_dotPos = DP_FINAL;
                iterateAndNextNull(nodep->rhsp());
                // if (debug() >= 9) nodep->dumpTree("-  dot-rho: ");
            }
            if (!m_ds.m_unresolvedClass) {
                if (start) {
                    AstNode* newp;
                    if (m_ds.m_dotErr) {
                        newp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
                    } else {
                        newp = nodep->rhsp()->unlinkFrBack();
                    }
                    if (debug() >= 9) newp->dumpTree("-  dot-out: ");
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                } else {  // Dot midpoint
                    AstNodeExpr* newp = nodep->rhsp()->unlinkFrBack();
                    if (m_ds.m_unresolvedCell) {
                        AstCellRef* const crp = new AstCellRef{
                            nodep->fileline(), nodep->name(), nodep->lhsp()->unlinkFrBack(), newp};
                        newp = crp;
                    }
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                }
            }
        }
        if (start) {
            m_ds = lastStates;
        } else {
            const bool unresolvedClass = m_ds.m_unresolvedClass;
            m_ds.m_dotp = lastStates.m_dotp;
            m_ds.m_unresolvedClass |= unresolvedClass;
        }
    }
    void visit(AstSenItem* nodep) override {
        VL_RESTORER(m_inSens);
        m_inSens = true;
        iterateChildren(nodep);
    }
    void visit(AstParseRef* nodep) override {
        if (nodep->user3SetOnce()) return;
        UINFO(9, "   linkPARSEREF " << m_ds.ascii() << "  n=" << nodep << endl);
        if (m_ds.m_unresolvedClass) return;
        // m_curSymp is symbol table of outer expression
        // m_ds.m_dotSymp is symbol table relative to "."'s above now
        UASSERT_OBJ(m_ds.m_dotSymp, nodep, "nullptr lookup symbol table");
        // Generally resolved during Primary, but might be at param time under AstUnlinkedRef
        UASSERT_OBJ(m_statep->forPrimary() || m_statep->forPrearray(), nodep,
                    "ParseRefs should no longer exist");
        const DotStates lastStates = m_ds;
        const bool start = (m_ds.m_dotPos == DP_NONE);  // Save, as m_dotp will be changed
        if (start) {
            m_ds.init(m_curSymp);
            // Note m_ds.m_dot remains nullptr; this is a reference not under a dot
        }
        if (nodep->name() == "super") {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: super");
            m_ds.m_dotErr = true;
        }
        if (nodep->name() == "this") {
            iterateChildren(nodep);
            if (m_statep->forPrimary()) return;  // The class might be parameterized somewhere
            const VSymEnt* classSymp = getThisClassSymp();
            if (!classSymp) {
                nodep->v3error("'this' used outside class (IEEE 1800-2017 8.11)");
                return;
            }
            AstClass* const classp = VN_AS(classSymp->nodep(), Class);
            AstClassRefDType* const dtypep
                = new AstClassRefDType{nodep->fileline(), classp, nullptr};
            AstThisRef* const newp = new AstThisRef{nodep->fileline(), VFlagChildDType{}, dtypep};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        if (m_ds.m_dotPos == DP_MEMBER && VN_IS(m_ds.m_dotp->lhsp(), LambdaArgRef)
            && nodep->name() == "index") {
            // 'with' statement's 'item.index'
            // m_ds.dotp->lhsp() was checked to know if `index` is directly after lambda arg ref.
            // If not, treat it as normal member select
            iterateChildren(nodep);
            const auto newp = new AstLambdaArgRef{
                nodep->fileline(), m_ds.m_dotp->lhsp()->name() + "__DOT__index", true};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        } else if (m_ds.m_dotPos == DP_MEMBER) {
            // Found a Var, everything following is membership.  {scope}.{var}.HERE {member}
            AstNodeExpr* const varEtcp = m_ds.m_dotp->lhsp()->unlinkFrBack();
            AstNodeExpr* const newp
                = new AstMemberSel{nodep->fileline(), varEtcp, VFlagChildDType{}, nodep->name()};
            if (m_ds.m_dotErr) {
                nodep->unlinkFrBack();  // Avoid circular node loop on errors
            } else {
                nodep->replaceWith(newp);
            }
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            //
            string expectWhat;
            bool allowScope = false;
            bool allowVar = false;
            bool allowFTask = false;
            bool staticAccess = false;
            if (m_ds.m_dotPos == DP_PACKAGE) {
                // {package}::{a}
                AstNodeModule* classOrPackagep = nullptr;
                expectWhat = "scope/variable/func";
                allowScope = true;
                allowVar = true;
                allowFTask = true;
                staticAccess = true;
                UASSERT_OBJ(VN_IS(m_ds.m_dotp->lhsp(), ClassOrPackageRef), m_ds.m_dotp->lhsp(),
                            "Bad package link");
                AstClassOrPackageRef* const cpackagerefp
                    = VN_AS(m_ds.m_dotp->lhsp(), ClassOrPackageRef);
                classOrPackagep = cpackagerefp->classOrPackagep();
                UASSERT_OBJ(classOrPackagep, m_ds.m_dotp->lhsp(), "Bad package link");
                m_ds.m_dotSymp = m_statep->getNodeSym(classOrPackagep);
                m_ds.m_dotPos = DP_SCOPE;
            } else if (m_ds.m_dotPos == DP_SCOPE) {
                // {a}.{b}, where {a} maybe a module name
                // or variable, where dotting into structure member
                expectWhat = "scope/variable";
                allowScope = true;
                allowVar = true;
            } else if (m_ds.m_dotPos == DP_NONE || m_ds.m_dotPos == DP_FINAL) {
                expectWhat = "variable";
                allowVar = true;
            } else {
                UINFO(1, "ds=" << m_ds.ascii() << endl);
                nodep->v3fatalSrc("Unhandled VParseRefExp");
            }
            // Lookup
            VSymEnt* foundp;
            string baddot;
            VSymEnt* okSymp = nullptr;
            if (allowScope) {
                foundp = m_statep->findDotted(nodep->fileline(), m_ds.m_dotSymp, nodep->name(),
                                              baddot, okSymp);  // Maybe nullptr
            } else {
                foundp = m_ds.m_dotSymp->findIdFallback(nodep->name());
            }
            if (foundp) {
                UINFO(9, "     found=se" << cvtToHex(foundp) << "  exp=" << expectWhat
                                         << "  n=" << foundp->nodep() << endl);
            }
            // What fell out?
            bool ok = false;
            // Special case: waiting on clocking event
            if (m_inSens && foundp && m_ds.m_dotPos != DP_SCOPE) {
                if (AstClocking* const clockingp = VN_CAST(foundp->nodep(), Clocking)) {
                    foundp = getCreateClockingEventSymEnt(clockingp);
                }
            }
            if (!foundp) {
            } else if (VN_IS(foundp->nodep(), Cell) || VN_IS(foundp->nodep(), Begin)
                       || VN_IS(foundp->nodep(), Netlist)  // for $root
                       || VN_IS(foundp->nodep(), Module)) {  // if top
                if (allowScope) {
                    ok = true;
                    m_ds.m_dotText = VString::dot(m_ds.m_dotText, ".", nodep->name());
                    m_ds.m_dotSymp = foundp;
                    m_ds.m_dotPos = DP_SCOPE;
                    // Upper AstDot visitor will handle it from here
                } else if (VN_IS(foundp->nodep(), Cell) && allowVar) {
                    AstCell* const cellp = VN_AS(foundp->nodep(), Cell);
                    if (VN_IS(cellp->modp(), Iface)) {
                        // Interfaces can be referenced like a variable for interconnect
                        VSymEnt* const cellEntp = m_statep->getNodeSym(cellp);
                        UASSERT_OBJ(cellEntp, nodep, "No interface sym entry");
                        VSymEnt* const parentEntp
                            = cellEntp->parentp();  // Container of the var; probably a module or
                                                    // generate begin
                        AstVar* const ifaceRefVarp
                            = findIfaceTopVarp(nodep, parentEntp, nodep->name());
                        //
                        ok = true;
                        m_ds.m_dotText = VString::dot(m_ds.m_dotText, ".", nodep->name());
                        m_ds.m_dotSymp = foundp;
                        m_ds.m_dotPos = DP_SCOPE;
                        UINFO(9, " cell -> iface varref " << foundp->nodep() << endl);
                        AstNode* const newp
                            = new AstVarRef{nodep->fileline(), ifaceRefVarp, VAccess::READ};
                        nodep->replaceWith(newp);
                        VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    } else if (VN_IS(cellp->modp(), NotFoundModule)) {
                        cellp->modNameFileline()->v3error("Cannot find file containing interface: "
                                                          << cellp->modp()->prettyNameQ());
                    }
                }
            } else if (allowFTask && VN_IS(foundp->nodep(), NodeFTask)) {
                AstTaskRef* const taskrefp
                    = new AstTaskRef{nodep->fileline(), nodep->name(), nullptr};
                nodep->replaceWith(taskrefp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                if (start) m_ds = lastStates;
                return;
            } else if (AstVar* const varp = foundToVarp(foundp, nodep, VAccess::READ)) {
                AstIfaceRefDType* const ifacerefp
                    = LinkDotState::ifaceRefFromArray(varp->subDTypep());
                if (ifacerefp && varp->isIfaceRef()) {
                    UASSERT_OBJ(ifacerefp->ifaceViaCellp(), ifacerefp, "Unlinked interface");
                    // Really this is a scope reference into an interface
                    UINFO(9, "varref-ifaceref " << m_ds.m_dotText << "  " << nodep << endl);
                    m_ds.m_dotText = VString::dot(m_ds.m_dotText, ".", nodep->name());
                    m_ds.m_dotSymp = m_statep->getNodeSym(ifacerefp->ifaceViaCellp());
                    m_ds.m_dotPos = DP_SCOPE;
                    ok = true;
                    AstNode* const newp = new AstVarRef{nodep->fileline(), varp, VAccess::READ};
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                } else if (allowVar) {
                    AstNode* newp;
                    if (m_ds.m_dotText != "") {
                        AstVarXRef* const refp
                            = new AstVarXRef{nodep->fileline(), nodep->name(), m_ds.m_dotText,
                                             VAccess::READ};  // lvalue'ness computed later
                        refp->varp(varp);
                        if (varp->attrSplitVar()) {
                            refp->v3warn(
                                SPLITVAR,
                                varp->prettyNameQ()
                                    << " has split_var metacomment but will not be split because"
                                    << " it is accessed from another module via a dot.");
                            varp->attrSplitVar(false);
                        }
                        m_ds.m_dotText = "";
                        if (m_ds.m_unresolvedCell && m_ds.m_unlinkedScopep) {
                            const string dotted = refp->dotted();
                            const size_t pos = dotted.find("__BRA__??__KET__");
                            // Arrays of interfaces all have the same parameters
                            if (pos != string::npos && varp->isParam()
                                && VN_IS(m_ds.m_unlinkedScopep, CellArrayRef)) {
                                refp->dotted(dotted.substr(0, pos));
                                newp = refp;
                            } else {
                                newp = new AstUnlinkedRef{nodep->fileline(), refp, refp->name(),
                                                          m_ds.m_unlinkedScopep->unlinkFrBack()};
                                m_ds.m_unlinkedScopep = nullptr;
                                m_ds.m_unresolvedCell = false;
                            }
                        } else {
                            newp = refp;
                        }
                    } else {
                        if (staticAccess && !varp->lifetime().isStatic() && !varp->isParam()) {
                            // TODO bug4077
                            // nodep->v3error("Static access to non-static member variable "
                            //                << varp->prettyNameQ() << endl);
                        }
                        AstVarRef* const refp = new AstVarRef{
                            nodep->fileline(), varp, VAccess::READ};  // lvalue'ness computed later
                        refp->classOrPackagep(foundp->classOrPackagep());
                        newp = refp;
                    }
                    UINFO(9, "    new " << newp << endl);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    m_ds.m_dotPos = DP_MEMBER;
                    ok = true;
                }
            } else if (const AstModport* const modportp = VN_CAST(foundp->nodep(), Modport)) {
                // A scope reference into an interface's modport (not
                // necessarily at a pin connection)
                UINFO(9, "cell-ref-to-modport " << m_ds.m_dotText << "  " << nodep << endl);
                UINFO(9, "unlinked " << m_ds.m_unlinkedScopep << endl);
                UINFO(9, "dotSymp " << m_ds.m_dotSymp << " " << m_ds.m_dotSymp->nodep() << endl);
                // Iface was the previously dotted component
                if (!m_ds.m_dotSymp || !VN_IS(m_ds.m_dotSymp->nodep(), Cell)
                    || !VN_AS(m_ds.m_dotSymp->nodep(), Cell)->modp()
                    || !VN_IS(VN_AS(m_ds.m_dotSymp->nodep(), Cell)->modp(), Iface)) {
                    nodep->v3error("Modport not referenced as <interface>."
                                   << modportp->prettyNameQ());
                } else if (!VN_AS(m_ds.m_dotSymp->nodep(), Cell)->modp()
                           || !VN_IS(VN_AS(m_ds.m_dotSymp->nodep(), Cell)->modp(), Iface)) {
                    nodep->v3error("Modport not referenced from underneath an interface: "
                                   << modportp->prettyNameQ());
                } else {
                    AstCell* const cellp = VN_AS(m_ds.m_dotSymp->nodep(), Cell);
                    UASSERT_OBJ(cellp, nodep, "Modport not referenced from an instance");
                    VSymEnt* const cellEntp = m_statep->getNodeSym(cellp);
                    UASSERT_OBJ(cellEntp, nodep, "No interface sym entry");
                    VSymEnt* const parentEntp
                        = cellEntp->parentp();  // Container of the var; probably a
                                                // module or generate begin
                    // We drop __BRA__??__KET__ as cells don't have that naming yet
                    AstVar* const ifaceRefVarp
                        = findIfaceTopVarp(nodep, parentEntp, cellp->name());
                    //
                    ok = true;
                    m_ds.m_dotText = VString::dot(m_ds.m_dotText, ".", nodep->name());
                    m_ds.m_dotSymp = foundp;
                    m_ds.m_dotPos = DP_SCOPE;
                    UINFO(9, " modport -> iface varref " << foundp->nodep() << endl);
                    // We lose the modport name here, so we cannot detect mismatched modports.
                    AstNodeExpr* newp
                        = new AstVarRef{nodep->fileline(), ifaceRefVarp, VAccess::READ};
                    auto* const cellarrayrefp = VN_CAST(m_ds.m_unlinkedScopep, CellArrayRef);
                    if (cellarrayrefp) {
                        // iface[vec].modport became CellArrayRef(iface, lsb)
                        // Convert back to SelBit(iface, lsb)
                        UINFO(9, " Array modport to SelBit " << cellarrayrefp << endl);
                        newp = new AstSelBit{cellarrayrefp->fileline(), newp,
                                             cellarrayrefp->selp()->unlinkFrBack()};
                        newp->user3(true);  // Don't process again
                        VL_DO_DANGLING(cellarrayrefp->unlinkFrBack(), cellarrayrefp);
                        m_ds.m_unlinkedScopep = nullptr;
                    }
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                }
            } else if (AstConstraint* const consp = VN_CAST(foundp->nodep(), Constraint)) {
                AstNode* const newp = new AstConstraintRef{nodep->fileline(), consp->name()};
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                ok = true;
                m_ds.m_dotPos = DP_MEMBER;
                m_ds.m_dotText = "";
            } else if (AstEnumItem* const valuep = VN_CAST(foundp->nodep(), EnumItem)) {
                if (allowVar) {
                    AstNode* const newp
                        = new AstEnumItemRef{nodep->fileline(), valuep, foundp->classOrPackagep()};
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    ok = true;
                    m_ds.m_dotText = "";
                }
            } else if (const AstLambdaArgRef* const argrefp
                       = VN_CAST(foundp->nodep(), LambdaArgRef)) {
                if (allowVar) {
                    AstNode* const newp
                        = new AstLambdaArgRef{nodep->fileline(), argrefp->name(), false};
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    ok = true;
                    m_ds.m_dotPos = DP_MEMBER;
                    m_ds.m_dotText = "";
                }
            } else if (VN_IS(foundp->nodep(), Clocking)) {
                m_ds.m_dotSymp = foundp;
                ok = m_ds.m_dotPos == DP_SCOPE;
            } else if (const AstNodeFTask* const ftaskp = VN_CAST(foundp->nodep(), NodeFTask)) {

                if (!ftaskp->isFunction() || ftaskp->classMethod()) {
                    ok = m_ds.m_dotPos == DP_NONE;
                    if (ok) {
                        // The condition is true for tasks,
                        // properties and void functions.
                        // In these cases, the parentheses may be skipped.
                        // Also SV class methods can be called without parens
                        AstFuncRef* const funcRefp
                            = new AstFuncRef{nodep->fileline(), nodep->name(), nullptr};
                        nodep->replaceWith(funcRefp);
                        VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    }
                }
            }
            if (!ok) {
                if (m_insideClassExtParam) {
                    // Don't throw error if the reference is inside a class that extends a param,
                    // because some members can't be linked in such a case. m_insideClassExtParam
                    // may be true only in the first stage of linking.
                    // Mark that the Dot statement can't be resolved.
                    m_ds.m_unresolvedClass = true;
                    // If the symbol was a scope name, it would be resolved.
                    if (m_ds.m_dotPos == DP_SCOPE) m_ds.m_dotPos = DP_MEMBER;
                } else {
                    // Cells/interfaces can't be implicit
                    const bool isCell = foundp ? VN_IS(foundp->nodep(), Cell) : false;
                    const bool checkImplicit = (!m_ds.m_dotp && m_ds.m_dotText == "" && !isCell);
                    const bool err
                        = !(checkImplicit && m_statep->implicitOk(m_modp, nodep->name()));
                    if (err) {
                        if (foundp) {
                            nodep->v3error("Found definition of '"
                                           << m_ds.m_dotText << (m_ds.m_dotText == "" ? "" : ".")
                                           << nodep->prettyName() << "'"
                                           << " as a " << foundp->nodep()->typeName()
                                           << " but expected a " << expectWhat);
                        } else if (m_ds.m_dotText == "") {
                            UINFO(7, "   ErrParseRef curSymp=se"
                                         << cvtToHex(m_curSymp) << " ds=" << m_ds.ascii() << endl);
                            const string suggest = m_statep->suggestSymFallback(
                                m_ds.m_dotSymp, nodep->name(), VNodeMatcher{});
                            nodep->v3error(
                                "Can't find definition of "
                                << expectWhat << ": " << nodep->prettyNameQ() << '\n'
                                << (suggest.empty() ? "" : nodep->warnMore() + suggest));
                        } else {
                            nodep->v3error("Can't find definition of "
                                           << (!baddot.empty() ? AstNode::prettyNameQ(baddot)
                                                               : nodep->prettyNameQ())
                                           << " in dotted " << expectWhat << ": '"
                                           << m_ds.m_dotText + "." + nodep->prettyName() << "'");
                            if (okSymp) {
                                okSymp->cellErrorScopes(nodep,
                                                        AstNode::prettyName(m_ds.m_dotText));
                            }
                        }
                        m_ds.m_dotErr = true;
                    }
                    if (checkImplicit) {
                        // Create if implicit, and also if error (so only complain once)
                        // Else if a scope is allowed, making a signal won't help error cascade
                        auto varp = createImplicitVar(m_curSymp, nodep, m_modp, m_modSymp, err);
                        AstVarRef* const newp
                            = new AstVarRef{nodep->fileline(), varp, VAccess::READ};
                        nodep->replaceWith(newp);
                        VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    }
                }
            }
        }
        if (start) m_ds = lastStates;
    }
    void visit(AstClassOrPackageRef* nodep) override {
        // Class: Recurse inside or cleanup not founds
        // checkNoDot not appropriate, can be under a dot
        m_usedPins.clear();
        UASSERT_OBJ(m_statep->forPrimary() || VN_IS(nodep->classOrPackageNodep(), ParamTypeDType)
                        || nodep->classOrPackagep(),
                    nodep, "ClassRef has unlinked class");
        UASSERT_OBJ(m_statep->forPrimary() || !nodep->paramsp(), nodep,
                    "class reference parameter not removed by V3Param");
        VL_RESTORER(m_ds);
        VL_RESTORER(m_pinSymp);

        // ClassRef's have pins, so track
        if (nodep->classOrPackagep()) {
            m_pinSymp = m_statep->getNodeSym(nodep->classOrPackagep());
        }
        AstClass* const refClassp = VN_CAST(nodep->classOrPackagep(), Class);
        // Make sure any extends() are properly imported within referenced class
        if (refClassp && !m_statep->forPrimary()) classExtendImport(refClassp);

        m_ds.init(m_curSymp);
        UINFO(4, "(Backto) Link ClassOrPackageRef: " << nodep << endl);
        iterateChildren(nodep);

        AstClass* const modClassp = VN_CAST(m_modp, Class);
        if (m_statep->forPrimary() && refClassp && !nodep->paramsp()
            && nodep->classOrPackagep()->hasGParam()
            // Don't warn on typedefs, which are hard to know if there's a param somewhere buried
            && VN_IS(nodep->classOrPackageNodep(), Class)
            // References to class:: within class itself are OK per IEEE (UVM does this)
            && modClassp != refClassp) {
            nodep->v3error("Reference to parameterized class without #() (IEEE 1800-2017 8.25.1)\n"
                           << nodep->warnMore() << "... Suggest use '"
                           << nodep->classOrPackageNodep()->prettyName() << "#()'");
        }
    }
    void visit(AstConstraintRef* nodep) override {
        if (nodep->user3SetOnce()) return;
        UINFO(8, "     " << nodep << endl);
        UINFO(8, "     " << m_ds.ascii() << endl);
        // No children defined
    }
    void visit(AstVarRef* nodep) override {
        // VarRef: Resolve its reference
        // ParseRefs are used the first pass (forPrimary) so we shouldn't get can't find
        // errors here now that we have a VarRef.
        // No checkNoDot; created and iterated from a parseRef
        iterateChildren(nodep);
        if (!nodep->varp()) {
            UINFO(9, " linkVarRef se" << cvtToHex(m_curSymp) << "  n=" << nodep << endl);
            UASSERT_OBJ(m_curSymp, nodep, "nullptr lookup symbol table");
            VSymEnt* const foundp = m_curSymp->findIdFallback(nodep->name());
            if (AstVar* const varp
                = foundp ? foundToVarp(foundp, nodep, nodep->access()) : nullptr) {
                nodep->varp(varp);
                updateVarUse(nodep->varp());
                // Generally set by parse, but might be an import
                nodep->classOrPackagep(foundp->classOrPackagep());
            }
            if (VL_UNCOVERABLE(!nodep->varp())) {
                nodep->v3error("Can't find definition of signal, again: "  // LCOV_EXCL_LINE
                               << nodep->prettyNameQ());
            }
        }
    }
    void visit(AstVarXRef* nodep) override {
        // VarRef: Resolve its reference
        // We always link even if varp() is set, because the module we choose may change
        // due to creating new modules, flattening, etc.
        if (nodep->user3SetOnce()) return;
        UINFO(8, "     " << nodep << endl);
        // No checkNoDot; created and iterated from a parseRef
        if (!m_modSymp) {
            // Module that is not in hierarchy.  We'll be dead code eliminating it later.
            UINFO(9, "Dead module for " << nodep << endl);
            nodep->varp(nullptr);
        } else {
            string baddot;
            VSymEnt* okSymp;
            VSymEnt* dotSymp = m_curSymp;  // Start search at current scope
            if (nodep->inlinedDots() != "") {  // Correct for current scope
                // Dotted lookup is always relative to module, as maybe
                // variable name lower down with same scope name we want to
                // ignore (t_math_divw)
                dotSymp = m_modSymp;
                const string inl = AstNode::dedotName(nodep->inlinedDots());
                dotSymp = m_statep->findDotted(nodep->fileline(), dotSymp, inl, baddot, okSymp);
                UASSERT_OBJ(dotSymp, nodep,
                            "Couldn't resolve inlined scope " << AstNode::prettyNameQ(baddot)
                                                              << " in: " << nodep->inlinedDots());
            }
            dotSymp = m_statep->findDotted(nodep->fileline(), dotSymp, nodep->dotted(), baddot,
                                           okSymp);  // Maybe nullptr
            if (!m_statep->forScopeCreation()) {
                VSymEnt* const foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
                AstVar* const varp
                    = foundp ? foundToVarp(foundp, nodep, nodep->access()) : nullptr;
                nodep->varp(varp);
                updateVarUse(nodep->varp());
                UINFO(7, "         Resolved " << nodep << endl);  // Also prints varp
                if (!nodep->varp()) {
                    nodep->v3error("Can't find definition of "
                                   << AstNode::prettyNameQ(baddot) << " in dotted signal: '"
                                   << nodep->dotted() + "." + nodep->prettyName() << "'");
                    okSymp->cellErrorScopes(nodep);
                    return;
                }
                // V3Inst may have expanded arrays of interfaces to
                // AstVarXRef's even though they are in the same module detect
                // this and convert to normal VarRefs
                if (!m_statep->forPrearray() && !m_statep->forScopeCreation()) {
                    if (VN_IS(nodep->dtypep(), IfaceRefDType)) {
                        AstVarRef* const newrefp
                            = new AstVarRef{nodep->fileline(), nodep->varp(), nodep->access()};
                        nodep->replaceWith(newrefp);
                        VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    }
                }
            } else {
                VSymEnt* const foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
                AstVarScope* vscp = foundp ? VN_AS(foundp->nodep(), VarScope) : nullptr;
                if (!vscp) {
                    nodep->v3error("Can't find varpin scope of "
                                   << AstNode::prettyNameQ(baddot) << " in dotted signal: '"
                                   << nodep->dotted() + "." + nodep->prettyName() << "'");
                    okSymp->cellErrorScopes(nodep);
                } else {
                    while (vscp->user2p()) {  // If V3Inline aliased it, pick up the new signal
                        UINFO(7, "         Resolved pre-alias " << vscp
                                                                << endl);  // Also prints taskp
                        vscp = VN_AS(vscp->user2p(), VarScope);
                    }
                    // Convert the VarXRef to a VarRef, so we don't need
                    // later optimizations to deal with VarXRef.
                    nodep->varp(vscp->varp());
                    nodep->varScopep(vscp);
                    updateVarUse(nodep->varp());
                    UINFO(7, "         Resolved " << nodep << endl);  // Also prints taskp
                    AstVarRef* const newvscp
                        = new AstVarRef{nodep->fileline(), vscp, nodep->access()};
                    nodep->replaceWith(newvscp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    UINFO(9, "         new " << newvscp << endl);  // Also prints taskp
                }
            }
        }
    }
    void visit(AstEnumDType* nodep) override {
        iterateChildren(nodep);
        AstRefDType* const refdtypep = VN_CAST(nodep->subDTypep(), RefDType);
        if (refdtypep && (nodep == refdtypep->subDTypep())) {
            refdtypep->v3error("Self-referential enumerated type definition");
        }
    }
    void visit(AstEnumItemRef* nodep) override {
        // EnumItemRef may be under a dot.  Should already be resolved.
        iterateChildren(nodep);
    }
    void visit(AstMethodCall* nodep) override {
        // Created here so should already be resolved.
        VL_RESTORER(m_ds);
        {
            m_ds.init(m_curSymp);
            iterateChildren(nodep);
        }
    }
    void visit(AstVar* nodep) override {
        checkNoDot(nodep);
        iterateChildren(nodep);
        if (m_statep->forPrimary() && nodep->isIO() && !m_ftaskp && !nodep->user4()) {
            nodep->v3error(
                "Input/output/inout does not appear in port list: " << nodep->prettyNameQ());
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->user3SetOnce()) return;
        UINFO(8, "     " << nodep << endl);
        UINFO(8, "     " << m_ds.ascii() << endl);
        {
            // Visit arguments at the beginning.
            // They may be visitted even if the current node can't be linked now.
            VL_RESTORER(m_ds);
            m_ds.init(m_curSymp);
            iterateChildren(nodep);
        }

        if (m_ds.m_super) {
            if (AstFuncRef* const funcRefp = VN_CAST(nodep, FuncRef)) {
                funcRefp->superReference(true);
            } else if (AstTaskRef* const taskRefp = VN_CAST(nodep, TaskRef)) {
                taskRefp->superReference(true);
            }
        }

        bool staticAccess = false;
        if (m_ds.m_unresolvedClass) {
            // Unable to link before V3Param
            return;
        } else if (m_ds.m_unresolvedCell && m_ds.m_dotPos == DP_FINAL && m_ds.m_unlinkedScopep) {
            AstNodeFTaskRef* const newftaskp = nodep->cloneTree(false);
            newftaskp->dotted(m_ds.m_dotText);
            AstNode* const newp = new AstUnlinkedRef{nodep->fileline(), newftaskp, nodep->name(),
                                                     m_ds.m_unlinkedScopep->unlinkFrBack()};
            m_ds.m_unlinkedScopep = nullptr;
            m_ds.m_unresolvedCell = false;
            nodep->replaceWith(newp);
            return;
        } else if (m_ds.m_dotp && m_ds.m_dotPos == DP_PACKAGE) {
            UASSERT_OBJ(VN_IS(m_ds.m_dotp->lhsp(), ClassOrPackageRef), m_ds.m_dotp->lhsp(),
                        "Bad package link");
            staticAccess = true;
            AstClassOrPackageRef* const cpackagerefp
                = VN_AS(m_ds.m_dotp->lhsp(), ClassOrPackageRef);
            if (cpackagerefp->name() == "local") {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: " << AstNode::prettyNameQ(cpackagerefp->name()));
            }
            UASSERT_OBJ(cpackagerefp->classOrPackagep(), m_ds.m_dotp->lhsp(), "Bad package link");
            nodep->classOrPackagep(cpackagerefp->classOrPackagep());
            // Class/package :: HERE function() . method_called_on_function_return_value()
            m_ds.m_dotPos = DP_MEMBER;
            m_ds.m_dotp = nullptr;
        } else if (m_ds.m_dotp && m_ds.m_dotPos == DP_FINAL) {
            nodep->dotted(m_ds.m_dotText);  // Maybe ""
        } else if (m_ds.m_dotp && m_ds.m_dotPos == DP_MEMBER) {
            // Found a Var, everything following is method call.
            // {scope}.{var}.HERE {method} ( ARGS )
            AstNodeExpr* const varEtcp = m_ds.m_dotp->lhsp()->unlinkFrBack();
            AstNodeExpr* argsp = nullptr;
            if (nodep->pinsp()) argsp = nodep->pinsp()->unlinkFrBackWithNext();
            AstNode* const newp = new AstMethodCall{nodep->fileline(), varEtcp, VFlagChildDType{},
                                                    nodep->name(), argsp};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        } else if (m_ds.m_dotp && m_ds.m_dotPos == DP_SCOPE) {
            // HERE function() . method_called_on_function_return_value()
            m_ds.m_dotPos = DP_MEMBER;
            m_ds.m_dotText = "";
        } else {
            checkNoDot(nodep);
        }
        if (nodep->classOrPackagep() && nodep->taskp()) {
            // References into packages don't care about cell hierarchy.
        } else if (!m_modSymp) {
            // Module that is not in hierarchy.  We'll be dead code eliminating it later.
            UINFO(9, "Dead module for " << nodep << endl);
            nodep->taskp(nullptr);
        } else if (nodep->dotted() == "" && nodep->taskp()) {
            // Earlier should have setup the links
            // Might be under a BEGIN we're not processing, so don't relink it
        } else {
            string baddot;
            VSymEnt* okSymp = nullptr;
            VSymEnt* dotSymp;
            if (nodep->dotted().empty()) {
                // Non-'super.' dotted reference
                dotSymp = m_ds.m_dotSymp;
            } else {
                // Start search at module, as a variable of same name under a subtask isn't a
                // relevant hit however a function under a begin/end is.  So we want begins, but
                // not the function
                dotSymp = m_curSymp;
            }
            if (nodep->classOrPackagep()) {  // Look only in specified package
                dotSymp = m_statep->getNodeSym(nodep->classOrPackagep());
                UINFO(8, "    Override classOrPackage " << dotSymp << endl);
            } else {
                if (nodep->inlinedDots() != "") {  // Correct for current scope
                    // Dotted lookup is always relative to module, as maybe
                    // variable name lower down with same scope name we want
                    // to ignore (t_math_divw)
                    dotSymp = m_modSymp;
                    const string inl = AstNode::dedotName(nodep->inlinedDots());
                    UINFO(8, "    Inlined " << inl << endl);
                    dotSymp
                        = m_statep->findDotted(nodep->fileline(), dotSymp, inl, baddot, okSymp);
                    if (!dotSymp) {
                        okSymp->cellErrorScopes(nodep);
                        nodep->v3fatalSrc("Couldn't resolve inlined scope "
                                          << AstNode::prettyNameQ(baddot)
                                          << " in: " << nodep->inlinedDots());
                    }
                }
                dotSymp = m_statep->findDotted(nodep->fileline(), dotSymp, nodep->dotted(), baddot,
                                               okSymp);  // Maybe nullptr
            }
            VSymEnt* const foundp = m_statep->findSymPrefixed(dotSymp, nodep->name(), baddot);
            AstNodeFTask* const taskp
                = foundp ? VN_CAST(foundp->nodep(), NodeFTask) : nullptr;  // Maybe nullptr
            if (taskp) {
                if (staticAccess && !taskp->isStatic()) {
                    // TODO bug4077
                    // nodep->v3error("Static access to non-static task/function "
                    //                << taskp->prettyNameQ() << endl);
                }
                nodep->taskp(taskp);
                nodep->classOrPackagep(foundp->classOrPackagep());
                UINFO(7, "         Resolved " << nodep << endl);  // Also prints taskp
            } else if (m_insideClassExtParam) {
                // The reference may point to a method declared in a super class, which is proved
                // by a parameter. In such a case, it can't be linked at the first stage.
                return;
            } else {
                // Note ParseRef has similar error handling/message output
                UINFO(7, "   ErrFtask curSymp=se" << cvtToHex(m_curSymp) << " dotSymp=se"
                                                  << cvtToHex(dotSymp) << endl);
                if (foundp) {
                    if (VN_IS(foundp->nodep(), Var) && m_ds.m_dotText == "" && m_ftaskp
                        && m_ftaskp->name() == foundp->nodep()->name()) {
                        // This is a recursive reference to the function itself, not to the var
                        nodep->taskp(m_ftaskp);
                        nodep->classOrPackagep(foundp->classOrPackagep());
                        UINFO(7, "         Resolved recursive " << nodep
                                                                << endl);  // Also prints taskp
                    } else {
                        nodep->v3error("Found definition of '"
                                       << m_ds.m_dotText << (m_ds.m_dotText == "" ? "" : ".")
                                       << nodep->prettyName() << "'"
                                       << " as a " << foundp->nodep()->typeName()
                                       << " but expected a task/function");
                    }
                } else if (VN_IS(nodep, New) && m_statep->forPrearray()) {
                    // Resolved in V3Width
                } else if (nodep->name() == "randomize" || nodep->name() == "srandom"
                           || nodep->name() == "get_randstate"
                           || nodep->name() == "set_randstate") {
                    if (AstClass* const classp = VN_CAST(m_modp, Class)) {
                        nodep->classOrPackagep(classp);
                    } else {
                        nodep->v3error("Calling implicit class method "
                                       << nodep->prettyNameQ() << " without being under class");
                        nodep->replaceWith(new AstConst{nodep->fileline(), 0});
                        VL_DO_DANGLING(pushDeletep(nodep), nodep);
                        return;
                    }
                } else if (nodep->dotted() == "") {
                    if (nodep->pli()) {
                        if (v3Global.opt.bboxSys()) {
                            AstNode* newp;
                            if (VN_IS(nodep, FuncRef)) {
                                newp = new AstConst{nodep->fileline(), AstConst::All0{}};
                            } else {
                                AstNode* outp = nullptr;
                                while (nodep->pinsp()) {
                                    AstNode* const pinp = nodep->pinsp()->unlinkFrBack();
                                    AstNode* addp = pinp;
                                    if (AstArg* const argp = VN_CAST(pinp, Arg)) {
                                        addp = argp->exprp()->unlinkFrBack();
                                        VL_DO_DANGLING(pinp->deleteTree(), pinp);
                                    }
                                    outp = AstNode::addNext(outp, addp);
                                }
                                newp = new AstSysIgnore{nodep->fileline(), outp};
                                newp->dtypep(nodep->dtypep());
                            }
                            nodep->replaceWith(newp);
                            VL_DO_DANGLING(nodep->deleteTree(), nodep);
                            return;
                        } else {
                            nodep->v3error(
                                "Unsupported or unknown PLI call: " << nodep->prettyNameQ());
                        }
                    } else {
                        const string suggest = m_statep->suggestSymFallback(
                            dotSymp, nodep->name(), LinkNodeMatcherFTask{});
                        nodep->v3error("Can't find definition of task/function: "
                                       << nodep->prettyNameQ() << '\n'
                                       << (suggest.empty() ? "" : nodep->warnMore() + suggest));
                    }
                } else {
                    const string suggest = m_statep->suggestSymFallback(dotSymp, nodep->name(),
                                                                        LinkNodeMatcherFTask{});
                    nodep->v3error("Can't find definition of "
                                   << AstNode::prettyNameQ(baddot) << " in dotted task/function: '"
                                   << nodep->dotted() + "." + nodep->prettyName() << "'\n"
                                   << (suggest.empty() ? "" : nodep->warnMore() + suggest));
                    okSymp->cellErrorScopes(nodep);
                }
            }
            taskFuncSwapCheck(nodep);
        }
    }
    void visit(AstSelBit* nodep) override {
        if (nodep->user3SetOnce()) return;
        iterateAndNextNull(nodep->fromp());
        if (m_ds.m_unresolvedClass) {
            UASSERT_OBJ(m_ds.m_dotPos != DP_SCOPE, nodep,
                        "Object of unresolved class on scope position in dotted reference");
            return;
        }
        if (m_ds.m_dotPos
            == DP_SCOPE) {  // Already under dot, so this is {modulepart} DOT {modulepart}
            UINFO(9, "  deferring until after a V3Param pass: " << nodep << endl);
            m_ds.m_dotText += "__BRA__??__KET__";
            m_ds.m_unresolvedCell = true;
            // And pass up m_ds.m_dotText
        }
        // Pass dot state down to fromp()
        iterateAndNextNull(nodep->fromp());
        {
            VL_RESTORER(m_ds);
            {
                m_ds.init(m_curSymp);
                iterateAndNextNull(nodep->bitp());
                iterateAndNextNull(nodep->attrp());
            }
        }
        if (m_ds.m_unresolvedCell && m_ds.m_dotPos == DP_SCOPE) {
            AstNodeExpr* const exprp = nodep->bitp()->unlinkFrBack();
            AstCellArrayRef* const newp
                = new AstCellArrayRef{nodep->fileline(), nodep->fromp()->name(), exprp};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstNodePreSel* nodep) override {
        // Excludes simple AstSelBit, see above
        if (nodep->user3SetOnce()) return;
        if (m_ds.m_dotPos
            == DP_SCOPE) {  // Already under dot, so this is {modulepart} DOT {modulepart}
            nodep->v3error("Syntax error: Range ':', '+:' etc are not allowed in the instance "
                           "part of a dotted reference");
            m_ds.m_dotErr = true;
            return;
        }
        iterateAndNextNull(nodep->fromp());
        VL_RESTORER(m_ds);
        {
            m_ds.init(m_curSymp);
            iterateAndNextNull(nodep->rhsp());
            iterateAndNextNull(nodep->thsp());
        }

        if (nodep->attrp()) {
            AstNode* const attrp = nodep->attrp()->unlinkFrBack();
            VL_DO_DANGLING(attrp->deleteTree(), attrp);
        }
        AstNode* const basefromp = AstArraySel::baseFromp(nodep, false);
        if (VN_IS(basefromp, Replicate)) {
            // From {...}[...] syntax in IEEE 2017
            if (basefromp) UINFO(1, "    Related node: " << basefromp << endl);
        } else {
            nodep->attrp(new AstAttrOf{nodep->fileline(), VAttrType::VAR_BASE,
                                       basefromp->cloneTree(false)});
        }
    }
    void visit(AstMemberSel* nodep) override {
        // checkNoDot not appropriate, can be under a dot
        iterateChildren(nodep);
    }
    void visit(AstNodeBlock* nodep) override {
        UINFO(5, "   " << nodep << endl);
        checkNoDot(nodep);
        VL_RESTORER(m_curSymp);
        {
            if (nodep->name() != "") {
                m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
                UINFO(5, "   cur=se" << cvtToHex(m_curSymp) << endl);
            }
            iterateChildren(nodep);
        }
        m_ds.m_dotSymp = VL_RESTORER_PREV(m_curSymp);
        UINFO(5, "   cur=se" << cvtToHex(m_curSymp) << endl);
    }
    void visit(AstNodeFTask* nodep) override {
        UINFO(5, "   " << nodep << endl);
        checkNoDot(nodep);
        if (nodep->isExternDef()) {
            if (const VSymEnt* const foundp
                = m_curSymp->findIdFallback("extern " + nodep->name())) {
                const AstNodeFTask* const funcProtop = VN_AS(foundp->nodep(), NodeFTask);
                // Copy specifiers.
                // External definition cannot have any specifiers, so no value will be overwritten.
                nodep->isHideLocal(funcProtop->isHideLocal());
                nodep->isHideProtected(funcProtop->isHideProtected());
                nodep->isStatic(funcProtop->isStatic());
                nodep->isVirtual(funcProtop->isVirtual());
                nodep->lifetime(funcProtop->lifetime());
            } else {
                nodep->v3error("extern not found that declares " + nodep->prettyNameQ());
            }
        }
        if (nodep->isExternProto()) {
            if (!m_curSymp->findIdFallback(nodep->name())) {
                nodep->v3error("Definition not found for extern " + nodep->prettyNameQ());
            }
        }
        VL_RESTORER(m_curSymp);
        {
            m_ftaskp = nodep;
            m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
            const bool isNew = nodep->name() == "new";
            if (isNew) m_explicitSuperNew = false;
            iterateChildren(nodep);
            if (isNew && !m_explicitSuperNew && m_statep->forParamed()) {
                const AstClassExtends* const classExtendsp = VN_AS(m_modp, Class)->extendsp();
                if (classExtendsp && classExtendsp->classOrNullp()) {
                    AstNodeStmt* const superNewp = addImplicitSuperNewCall(VN_AS(nodep, Func));
                    iterate(superNewp);
                }
            }
        }
        m_ds.m_dotSymp = VL_RESTORER_PREV(m_curSymp);
        m_ftaskp = nullptr;
    }
    void visit(AstNodeForeach* nodep) override {
        UINFO(5, "   " << nodep << endl);
        checkNoDot(nodep);
        VL_RESTORER(m_curSymp);
        {
            m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
            iterateChildren(nodep);
        }
        m_ds.m_dotSymp = VL_RESTORER_PREV(m_curSymp);
    }
    void visit(AstWith* nodep) override {
        UINFO(5, "   " << nodep << endl);
        checkNoDot(nodep);
        VL_RESTORER(m_curSymp);
        {
            m_ds.m_dotSymp = m_curSymp = m_statep->getNodeSym(nodep);
            iterateChildren(nodep);
        }
        m_ds.m_dotSymp = VL_RESTORER_PREV(m_curSymp);
    }
    void visit(AstLambdaArgRef* nodep) override {
        UINFO(5, "   " << nodep << endl);
        // No checknodot(nodep), visit(AstScope) will check for LambdaArgRef
        iterateChildren(nodep);
    }
    void visit(AstClassExtends* nodep) override {
        // Resolve the symbol and get the class.
        // If it is a parameterized case, the class will be resolved after V3Param.cpp
        if (nodep->user3SetOnce()) return;
        // If the class is resolved, there is nothing more to do
        if (nodep->classOrNullp()) return;
        if (m_statep->forPrimary()) {
            AstNode* cprp = nodep->classOrPkgsp();
            VSymEnt* lookSymp = m_curSymp;
            if (AstDot* const dotp = VN_CAST(cprp, Dot)) {
                dotp->user3(true);
                if (AstClassOrPackageRef* lookNodep = VN_CAST(dotp->lhsp(), ClassOrPackageRef)) {
                    iterate(lookNodep);
                    cprp = dotp->rhsp();
                    lookSymp = m_statep->getNodeSym(lookNodep->classOrPackagep());
                } else {
                    dotp->lhsp()->v3error("Attempting to extend"  // LCOV_EXCL_LINE
                                          " using non-class under dot");
                }
            }
            AstClassOrPackageRef* const cpackagerefp = VN_CAST(cprp, ClassOrPackageRef);
            if (VL_UNCOVERABLE(!cpackagerefp)) {
                // Linking the extend gives an error before this is hit
                nodep->v3error("Attempting to extend using non-class");  // LCOV_EXCL_LINE
                return;
            }
            VSymEnt* const foundp = lookSymp->findIdFallback(cpackagerefp->name());
            if (foundp) {
                if (AstClass* const classp = VN_CAST(foundp->nodep(), Class)) {
                    AstPin* paramsp = cpackagerefp->paramsp();
                    if (paramsp) {
                        paramsp = paramsp->cloneTree(true);
                        nodep->parameterized(true);
                    }
                    nodep->childDTypep(new AstClassRefDType{nodep->fileline(), classp, paramsp});
                    // Link pins
                    iterate(nodep->childDTypep());
                } else if (AstParamTypeDType* const paramp
                           = VN_CAST(foundp->nodep(), ParamTypeDType)) {
                    AstRefDType* const refParamp
                        = new AstRefDType{nodep->fileline(), paramp->name()};
                    refParamp->refDTypep(paramp);
                    nodep->childDTypep(refParamp);
                    nodep->parameterized(true);
                } else {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: " << foundp->nodep()->prettyTypeName()
                                                  << " in AstClassExtends");
                    return;
                }
            } else {
                const string suggest = m_statep->suggestSymFallback(
                    m_curSymp, cpackagerefp->name(), LinkNodeMatcherClass{});
                cpackagerefp->v3error(
                    "Class for '" << nodep->verilogKwd()  // extends/implements
                                  << "' not found: " << cpackagerefp->prettyNameQ() << '\n'
                                  << (suggest.empty() ? "" : cpackagerefp->warnMore() + suggest));
                return;
            }
            if (!nodep->childDTypep()) nodep->v3error("Attempting to extend using non-class");
            nodep->classOrPkgsp()->unlinkFrBack()->deleteTree();
        } else {
            // Probably a parameter
            if (AstRefDType* const refp = VN_CAST(nodep->childDTypep(), RefDType)) {
                if (AstClassRefDType* classRefp = VN_CAST(refp->skipRefp(), ClassRefDType)) {
                    // Resolved to a class reference.
                    refp->replaceWith(classRefp->cloneTree(false));
                } else {
                    // Unable to resolve the ref type to a class reference.
                    // Get the value of type parameter passed to the class instance,
                    // to print the helpful error message.
                    const AstNodeDType* typep = refp->refDTypep();
                    if (const AstParamTypeDType* const paramp = VN_CAST(typep, ParamTypeDType)) {
                        typep = paramp->subDTypep();
                    }
                    typep->v3error("Attempting to extend using non-class");
                }
            }
        }
    }
    void visit(AstClass* nodep) override {
        if (nodep->user3SetOnce()) return;
        UINFO(5, "   " << nodep << endl);
        checkNoDot(nodep);
        VL_RESTORER(m_curSymp);
        VL_RESTORER(m_modSymp);
        VL_RESTORER(m_modp);
        VL_RESTORER(m_ifClassImpNames);
        VL_RESTORER(m_insideClassExtParam);
        {
            m_ds.init(m_curSymp);
            // Until overridden by a SCOPE
            m_ds.m_dotSymp = m_curSymp = m_modSymp = m_statep->getNodeSym(nodep);
            m_modp = nodep;
            int next = 0;
            for (AstClassExtends* cextp = nodep->extendsp(); cextp;
                 cextp = VN_AS(cextp->nextp(), ClassExtends)) {
                // Replace abstract reference with hard pointer
                // Will need later resolution when deal with parameters
                if (++next == 2 && !nodep->isInterfaceClass() && !cextp->isImplements()) {
                    cextp->v3error("Multiple inheritance illegal on non-interface classes"
                                   " (IEEE 1800-2017 8.13)");
                }
                iterate(cextp);
                if (m_statep->forPrimary()) {
                    if (cextp->parameterized()) {
                        // Parameters in extends statement.
                        // The class can't be resolved in the current pass.
                        m_extendsParam.insert(nodep);
                        m_insideClassExtParam = true;
                    }
                    if (AstClassRefDType* const classRefp
                        = VN_CAST(cextp->childDTypep(), ClassRefDType)) {
                        AstClass* const classp = classRefp->classp();
                        if (classp != nodep) iterate(classp);
                        if (m_extendsParam.find(classp) != m_extendsParam.end()) {
                            // One of its super classes has parameters in extends statement.
                            // Some links may not be resolved in the first pass.
                            m_extendsParam.insert(nodep);
                            m_insideClassExtParam = true;
                        }
                    }
                }

                if (AstClass* const baseClassp = cextp->classOrNullp()) {
                    // Already converted. Update symbol table to link unlinked members.
                    // Base class has to be visited in a case if its extends statement
                    // needs to be handled. Recursive inheritance was already checked.
                    // Must be here instead of in LinkDotParam to handle
                    // "class (type T) extends T".
                    if (baseClassp == nodep) {
                        cextp->v3error("Attempting to extend class " << nodep->prettyNameQ()
                                                                     << " from itself");
                    } else if (cextp->isImplements() && !baseClassp->isInterfaceClass()) {
                        cextp->v3error("Attempting to implement from non-interface class "
                                       << baseClassp->prettyNameQ() << '\n'
                                       << "... Suggest use 'extends'");
                    } else if (!cextp->isImplements() && !nodep->isInterfaceClass()
                               && baseClassp->isInterfaceClass()) {
                        cextp->v3error("Attempting to extend from interface class "
                                       << baseClassp->prettyNameQ() << '\n'
                                       << "... Suggest use 'implements'");
                    }
                    baseClassp->isExtended(true);
                    nodep->isExtended(true);
                    iterate(baseClassp);
                    importSymbolsFromExtended(nodep, cextp);
                    continue;
                }
            }
            m_ds.m_dotSymp = m_curSymp;

            iterateChildren(nodep);
        }
        // V3Width when determines types needs to find enum values and such
        // so add members pointing to appropriate enum values
        {
            VMemberMap memberMap;
            for (VSymEnt::const_iterator it = m_curSymp->begin(); it != m_curSymp->end(); ++it) {
                AstNode* const itemp = it->second->nodep();
                if (!memberMap.findMember(nodep, it->first)) {
                    if (AstEnumItem* const aitemp = VN_CAST(itemp, EnumItem)) {
                        AstEnumItemRef* const newp = new AstEnumItemRef{
                            aitemp->fileline(), aitemp, it->second->classOrPackagep()};
                        UINFO(8, "Class import noderef '" << it->first << "' " << newp << endl);
                        nodep->addMembersp(newp);
                        memberMap.insert(nodep, newp);
                    }
                }
            }
        }
        m_ds.m_dotSymp = VL_RESTORER_PREV(m_curSymp);
    }
    void visit(AstRefDType* nodep) override {
        // Resolve its reference
        if (nodep->user3SetOnce()) return;
        if (AstNode* const cpackagep = nodep->classOrPackageOpp()) {
            if (AstClassOrPackageRef* const cpackagerefp = VN_CAST(cpackagep, ClassOrPackageRef)) {
                const AstClass* const clsp = VN_CAST(cpackagerefp->classOrPackageNodep(), Class);
                if (clsp && clsp->isParameterized()) {
                    // Unable to link before the instantiation of parameter classes.
                    // The class reference node has to be visited to properly link parameters.
                    iterate(cpackagep);
                    return;
                }
                nodep->classOrPackagep(cpackagerefp->classOrPackagep());
                if (!VN_IS(nodep->classOrPackagep(), Class)
                    && !VN_IS(nodep->classOrPackagep(), Package)) {
                    cpackagerefp->v3error(
                        "'::' expected to reference a class/package but referenced '"
                        << (nodep->classOrPackagep() ? nodep->classOrPackagep()->prettyTypeName()
                                                     : "<unresolved-object>")
                        << "'\n"
                        << cpackagerefp->warnMore() + "... Suggest '.' instead of '::'");
                }
            } else {
                cpackagep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Multiple '::' package/class reference");
            }
            VL_DO_DANGLING(cpackagep->unlinkFrBack()->deleteTree(), cpackagep);
        }
        if (m_ds.m_dotp && m_ds.m_dotPos == DP_PACKAGE) {
            UASSERT_OBJ(VN_IS(m_ds.m_dotp->lhsp(), ClassOrPackageRef), m_ds.m_dotp->lhsp(),
                        "Bad package link");
            auto* const cpackagerefp = VN_AS(m_ds.m_dotp->lhsp(), ClassOrPackageRef);
            UASSERT_OBJ(cpackagerefp->classOrPackagep(), m_ds.m_dotp->lhsp(), "Bad package link");
            nodep->classOrPackagep(cpackagerefp->classOrPackagep());
            m_ds.m_dotPos = DP_SCOPE;
            m_ds.m_dotp = nullptr;
        } else {
            checkNoDot(nodep);
        }
        if (nodep->typeofp()) {  // Really is a typeof not a reference
        } else if (!nodep->typedefp() && !nodep->subDTypep()) {
            const VSymEnt* foundp;
            if (nodep->classOrPackagep()) {
                foundp = m_statep->getNodeSym(nodep->classOrPackagep())->findIdFlat(nodep->name());
            } else {
                foundp = m_curSymp->findIdFallback(nodep->name());
            }
            if (AstTypedef* const defp = foundp ? VN_CAST(foundp->nodep(), Typedef) : nullptr) {
                nodep->typedefp(defp);
                nodep->classOrPackagep(foundp->classOrPackagep());
            } else if (AstParamTypeDType* const defp
                       = foundp ? VN_CAST(foundp->nodep(), ParamTypeDType) : nullptr) {
                if (defp == nodep->backp()) {  // Where backp is typically typedef
                    nodep->v3error("Reference to '" << m_ds.m_dotText
                                                    << (m_ds.m_dotText == "" ? "" : ".")
                                                    << nodep->prettyName() << "'"
                                                    << " type would form a recursive definition");
                    nodep->refDTypep(nodep->findVoidDType());  // Try to reduce later errors
                } else {
                    nodep->refDTypep(defp);
                    nodep->classOrPackagep(foundp->classOrPackagep());
                }
            } else if (AstClass* const defp = foundp ? VN_AS(foundp->nodep(), Class) : nullptr) {
                AstPin* const paramsp = nodep->paramsp();
                if (paramsp) paramsp->unlinkFrBackWithNext();
                AstClassRefDType* const newp
                    = new AstClassRefDType{nodep->fileline(), defp, paramsp};
                newp->classOrPackagep(foundp->classOrPackagep());
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else if (m_insideClassExtParam) {
                return;
            } else {
                if (foundp) UINFO(1, "Found sym node: " << foundp->nodep() << endl);
                nodep->v3error("Can't find typedef: " << nodep->prettyNameQ());
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstDpiExport* nodep) override {
        // AstDpiExport: Make sure the function referenced exists, then dump it
        iterateChildren(nodep);
        checkNoDot(nodep);
        VSymEnt* const foundp = m_curSymp->findIdFallback(nodep->name());
        AstNodeFTask* const taskp = foundp ? VN_AS(foundp->nodep(), NodeFTask) : nullptr;
        if (!taskp) {
            nodep->v3error(
                "Can't find definition of exported task/function: " << nodep->prettyNameQ());
        } else if (taskp->dpiExport()) {
            nodep->v3error("Function was already DPI Exported, duplicate not allowed: "
                           << nodep->prettyNameQ());
        } else {
            taskp->dpiExport(true);
            if (nodep->cname() != "") taskp->cname(nodep->cname());
        }
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstPackageImport* nodep) override {
        // No longer needed
        checkNoDot(nodep);
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstPackageExport* nodep) override {
        // No longer needed
        checkNoDot(nodep);
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstPackageExportStarStar* nodep) override {
        // No longer needed
        checkNoDot(nodep);
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstCellRef* nodep) override {
        UINFO(5, "  AstCellRef: " << nodep << " " << m_ds.ascii() << endl);
        iterateChildren(nodep);
    }
    void visit(AstCellArrayRef* nodep) override {
        UINFO(5, "  AstCellArrayRef: " << nodep << " " << m_ds.ascii() << endl);
        // Expression already iterated
    }
    void visit(AstUnlinkedRef* nodep) override {
        UINFO(5, "  AstCellArrayRef: " << nodep << " " << m_ds.ascii() << endl);
        // No need to iterate, if we have a UnlinkedVarXRef, we're already done
    }
    void visit(AstStmtExpr* nodep) override {
        checkNoDot(nodep);
        // Check if nodep represents a super.new call;
        if (VN_IS(nodep->exprp(), New)) {
            // in this case it was already linked, so it doesn't have a super reference
            m_explicitSuperNew = true;
        } else if (const AstDot* const dotp = VN_CAST(nodep->exprp(), Dot)) {
            if (dotp->lhsp()->name() == "super" && VN_IS(dotp->rhsp(), New)) {
                m_explicitSuperNew = true;
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstAttrOf* nodep) override { iterateChildren(nodep); }

    void visit(AstNode* nodep) override {
        checkNoDot(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    LinkDotResolveVisitor(AstNetlist* rootp, LinkDotState* statep)
        : m_statep{statep} {
        UINFO(4, __FUNCTION__ << ": " << endl);
        iterate(rootp);
    }
    ~LinkDotResolveVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkDot::linkDotGuts(AstNetlist* rootp, VLinkDotStep step) {
    VIsCached::clearCacheTree();  // Avoid using any stale isPure
    if (debug() >= 5 || dumpTreeLevel() >= 9) {
        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot.tree"));
    }
    LinkDotState state{rootp, step};
    const LinkDotFindVisitor visitor{rootp, &state};
    if (debug() >= 5 || dumpTreeLevel() >= 9) {
        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-find.tree"));
    }
    if (step == LDS_PRIMARY || step == LDS_PARAMED) {
        // Initial link stage, resolve parameters
        const LinkDotParamVisitor visitors{rootp, &state};
        if (debug() >= 5 || dumpTreeLevel() >= 9) {
            v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-param.tree"));
        }
    } else if (step == LDS_ARRAYED) {
    } else if (step == LDS_SCOPED) {
        // Well after the initial link when we're ready to operate on the flat design,
        // process AstScope's.  This needs to be separate pass after whole hierarchy graph created.
        const LinkDotScopeVisitor visitors{rootp, &state};
        v3Global.assertScoped(true);
        if (debug() >= 5 || dumpTreeLevel() >= 9) {
            v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("prelinkdot-scoped.tree"));
        }
    } else {
        v3fatalSrc("Bad case");
    }
    state.dumpSelf();
    state.computeIfaceModSyms();
    state.computeIfaceVarSyms();
    state.computeScopeAliases();
    state.dumpSelf();
    { LinkDotResolveVisitor{rootp, &state}; }
    state.dumpSelf();
}

void V3LinkDot::linkDotPrimary(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    linkDotGuts(nodep, LDS_PRIMARY);
    V3Global::dumpCheckGlobalTree("linkdot", 0, dumpTreeLevel() >= 6);
}

void V3LinkDot::linkDotParamed(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    linkDotGuts(nodep, LDS_PARAMED);
    V3Global::dumpCheckGlobalTree("linkdotparam", 0, dumpTreeLevel() >= 3);
}

void V3LinkDot::linkDotArrayed(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    linkDotGuts(nodep, LDS_ARRAYED);
    V3Global::dumpCheckGlobalTree("linkdot", 0, dumpTreeLevel() >= 6);
}

void V3LinkDot::linkDotScope(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    linkDotGuts(nodep, LDS_SCOPED);
    V3Global::dumpCheckGlobalTree("linkdot", 0, dumpTreeLevel() >= 3);
}
