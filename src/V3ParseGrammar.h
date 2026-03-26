// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse syntax tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3Ast.h"
#include "V3CoverAtat.h"
#include "V3Control.h"
#include "V3Global.h"
#include "V3ParseImp.h"  // Defines YYTYPE; before including bison header

#include <algorithm>
#include <iterator>
#include <limits>
#include <stack>
#include <unordered_map>
#include <vector>

class V3ParseGrammar final {
public:
    enum class CoverBinKind : uint8_t { NORMAL, IGNORE, ILLEGAL, DEFAULT };
    enum class CoverTransRepeatKind : uint8_t { NONE, CONSEC, GOTO, NONCONSEC };
    struct CoverGroupCoverageMethod final {
        AstFunc* funcp = nullptr;
        AstVar* returnVarp = nullptr;
        AstVar* coveredBinsArgp = nullptr;
        AstVar* totalBinsArgp = nullptr;
    };
    struct CoverGroupMethods final {
        AstVar* defaultIntVarp = nullptr;
        AstVar* optionVarp = nullptr;
        AstVar* typeOptionVarp = nullptr;
        AstVar* instNameVarp = nullptr;
        AstVar* typeMergeInstancesVarp = nullptr;
        AstVar* instCountVarp = nullptr;
        AstVar* instCoveredSumVarp = nullptr;
        AstVar* instTotalSumVarp = nullptr;
        AstVar* instPrevCoveredVarp = nullptr;
        AstVar* instPrevTotalVarp = nullptr;
        AstFunc* sampleFuncp = nullptr;
        AstFunc* startFuncp = nullptr;
        AstFunc* stopFuncp = nullptr;
        AstFunc* setInstNameFuncp = nullptr;
        AstVar* setInstNameArgp = nullptr;
        CoverGroupCoverageMethod typeCoverage;
        CoverGroupCoverageMethod typeCoverageAlias;
        CoverGroupCoverageMethod instCoverage;
    };
    struct CoverpointPendingOption final {
        FileLine* flp = nullptr;
        bool typeOption = false;
        std::string member;
        AstNodeExpr* valuep = nullptr;
    };
    struct CoverBinSpec final {
        FileLine* flp = nullptr;
        std::string name;
        AstNodeExpr* valueItemsp = nullptr;
        AstNode* transItemsp = nullptr;
        AstNodeExpr* transRepeatValueItemsp = nullptr;
        AstNodeExpr* withp = nullptr;
        AstNodeExpr* iffp = nullptr;
        AstNodeExpr* arraySizep = nullptr;
        CoverBinKind kind = CoverBinKind::NORMAL;
        CoverTransRepeatKind transRepeatKind = CoverTransRepeatKind::NONE;
        int transRepeatMin = 0;
        int transRepeatMax = 0;
        bool wildcard = false;
        bool transition = false;
        bool unsizedArray = false;
        bool defaultSequence = false;
        AstVar* transCountVarp = nullptr;
    };
    struct CoverpointBinInfo final {
        std::string name;
        int binNum = 0;
        AstNodeExpr* condp = nullptr;
        AstNodeExpr* valueItemsp = nullptr;
    };
    struct CoverpointInfo final {
        std::string name;
        AstVar* instVarp = nullptr;
        AstVar* typeVarp = nullptr;
        AstVar* lastBinVarp = nullptr;
        int totalBins = 0;
        std::vector<CoverpointBinInfo> bins;
    };
    struct CoverCrossSelection final {
        std::string coverpointName;
        std::vector<std::string> binNames;
        bool selectNone = false;
        bool invert = false;
    };
    struct CoverCrossClause final {
        std::vector<CoverCrossSelection> selections;
        AstNodeExpr* iffp = nullptr;
    };
    struct CoverCrossBinSpec final {
        FileLine* flp = nullptr;
        std::string name;
        std::vector<CoverCrossClause> clauses;
        AstNodeExpr* iffp = nullptr;
        CoverBinKind kind = CoverBinKind::NORMAL;
    };
    struct CoverpointState final {
        bool active = false;
        bool unsupported = false;
        FileLine* flp = nullptr;
        std::string name;
        AstNodeExpr* exprp = nullptr;
        AstNodeExpr* iffp = nullptr;
        AstVar* prevVarp = nullptr;
        AstVar* prevValidVarp = nullptr;
        std::vector<CoverBinSpec> bins;
        std::vector<CoverpointPendingOption> options;
    };
    struct CovergroupState final {
        bool active = false;
        bool eventDriven = false;
        bool extendsUnsupported = false;
        bool ownerInClass = false;
        int autoCoverpointNum = 0;
        int autoCrossNum = 0;
        int hiddenSampleArgNum = 0;
        AstClass* classp = nullptr;
        AstClass* ownerClassp = nullptr;
        AstFunc* ctorp = nullptr;
        ::AstSenTree* eventSenTreep = nullptr;
        ::AstArg* autoSampleArgsp = nullptr;
        struct AtAtHook final {
            bool begin = false;
            std::string target;
        };
        std::vector<AtAtHook> atatHooks;
        CoverGroupMethods methods;
        std::vector<CoverpointPendingOption> options;
        std::unordered_map<std::string, AstVar*> sampleVars;
        std::unordered_map<std::string, AstVar*> ctorBoundVars;
        std::vector<CoverpointInfo> coverpoints;
    };
    struct CoverCrossState final {
        bool active = false;
        bool unsupported = false;
        FileLine* flp = nullptr;
        std::string name;
        AstNodeExpr* iffp = nullptr;
        std::vector<const CoverpointInfo*> infos;
        std::vector<CoverpointInfo> implicitInfos;
        std::vector<CoverCrossBinSpec> bins;
        std::vector<CoverpointPendingOption> options;
        int crossNumPrintMissing = 0;
    };
    struct CovergroupAutoSample final {
        ::AstSenTree* sentreep = nullptr;
        ::AstArg* argsp = nullptr;
        AstFunc* sampleFuncp = nullptr;
        std::vector<CovergroupState::AtAtHook> atatHooks;
    };

    AstVar* m_varAttrp = nullptr;  // Current variable for attribute adding
    AstRange* m_gateRangep = nullptr;  // Current range for gate declarations
    AstNode* m_scopedSigAttr = nullptr;  // Pointer to default signal attribute
    AstCase* m_caseAttrp = nullptr;  // Current case statement for attribute adding
    AstNodeDType* m_varDTypep = nullptr;  // Pointer to data type for next signal declaration
    AstNodeDType* m_memDTypep = nullptr;  // Pointer to data type for next member declaration
    AstDelay* m_netDelayp = nullptr;  // Pointer to delay for next signal declaration
    AstStrengthSpec* m_netStrengthp = nullptr;  // Pointer to strength for next net declaration
    FileLine* m_instModuleFl = nullptr;  // Fileline of module referenced for instantiations
    AstPin* m_instParamp = nullptr;  // Parameters for instantiations
    string m_instModule;  // Name of module referenced for instantiations
    VVarType m_varDecl = VVarType::UNKNOWN;  // Type for next signal declaration (reg/wire/etc)
    VDirection m_varIO = VDirection::NONE;  // Direction for next signal declaration (reg/wire/etc)
    VLifetime m_varLifetime;  // Static/Automatic for next signal
    V3Control::VarSpecKind m_vltVarSpecKind = V3Control::VarSpecKind::VAR;
    bool m_impliedDecl = false;  // Allow implied wire declarations
    bool m_varDeclTyped = false;  // Var got reg/wire for dedup check
    bool m_pinAnsi = false;  // In ANSI parameter or port list
    bool m_tracingParse = true;  // Tracing disable for parser
    bool m_inImplements = false;  // Is inside class implements list
    bool m_insideProperty = false;  // Is inside property declaration
    bool m_specifyignWarned = false;  // Issued a SPECIFYIGN warning
    bool m_typedPropertyPort = false;  // Typed property port occurred on port lists
    bool m_modportImpExpActive
        = false;  // Standalone ID is a tf_identifier instead of port_identifier
    bool m_modportImpExpLastIsExport
        = false;  // Last import_export statement in modportPortsDecl is an export
    AstNode* m_modportProtoTasksp
        = nullptr;  // Prototype tasks from modport import/export with prototype
    int m_classDepth = 0;  // Nested class declaration depth currently being parsed

    int m_pinNum = -1;  // Pin number currently parsing
    std::stack<int> m_pinStack;  // Queue of pin numbers being parsed

    CovergroupState m_covergroup;
    CoverpointState m_coverpoint;
    CoverCrossState m_covercross;
    std::vector<AstVar*> m_declaredVars;
    std::unordered_map<std::string, CovergroupAutoSample> m_covergroupAutoSamples;
    std::unordered_map<std::string, AstArg*> m_covergroupImplicitSampleArgs;
    std::vector<AstClass*> m_classStack;
    std::vector<AstClassExtends*> m_pendingClassExtendsStack;

    static int s_typeImpNum;  // Implicit type number, incremented each module

    // CONSTRUCTORS
    V3ParseGrammar() {}
    static V3ParseGrammar* singletonp() {
        static V3ParseGrammar singleton;
        return &singleton;
    }
    static bool makeCovergroupAtAtSampleStmt(AstVar* varp,
                                             std::vector<std::pair<std::string, bool>>& hooks,
                                             AstNode*& stmtp) {
        return singletonp()->makeCovergroupAtAtSampleStmtImpl(varp, hooks, stmtp);
    }

    // METHODS
    AstArg* argWrapList(AstNodeExpr* nodep) VL_MT_DISABLED;
    bool allTracingOn(const FileLine* fl) const {
        return v3Global.opt.trace() && m_tracingParse && fl->tracingOn();
    }
    AstRange* scrubRange(AstNodeRange* rangep) VL_MT_DISABLED;
    AstNodePreSel* scrubSel(AstNodeExpr* fromp, AstNodePreSel* selp) VL_MT_DISABLED;
    AstNodeDType* createArray(AstNodeDType* basep, AstNodeRange* rangep,
                              bool isPacked) VL_MT_DISABLED;
    AstVar* createVariable(FileLine* fileline, const string& name, AstNodeRange* arrayp,
                           AstNode* attrsp) VL_MT_DISABLED;
    AstAssignW* createSupplyExpr(FileLine* fileline, const string& name, int value) VL_MT_DISABLED;
    std::string textQuoted(FileLine* fileline, const std::string& text) {
        return singletonp()->unquoteString(fileline, text);
    }
    AstNode* createCell(FileLine* fileline, const string& name, AstPin* pinlistp,
                        AstNodeRange* rangelistp) {
        // Must clone m_instParamp as may be comma'ed list of instances
        AstCell* const nodep = new AstCell{
            fileline,
            singletonp()->m_instModuleFl,
            name,
            singletonp()->m_instModule,
            pinlistp,
            (singletonp()->m_instParamp ? singletonp()->m_instParamp->cloneTree(true) : nullptr),
            singletonp()->scrubRange(rangelistp)};
        nodep->trace(singletonp()->allTracingOn(fileline));
        return nodep;
    }
    static AstNodeExpr* makeCoverpointMemberSel(FileLine* fl, AstNodeExpr* fromp,
                                                const string& member, const VAccess& access) {
        AstMemberSel* const selp = new AstMemberSel{fl, fromp, VFlagChildDType{}, member};
        selp->access(access);
        return selp;
    }
    static void deleteCoverBinSpec(CoverBinSpec& bin) {
        if (bin.valueItemsp) VL_DO_DANGLING(bin.valueItemsp->deleteTree(), bin.valueItemsp);
        if (bin.transItemsp) VL_DO_DANGLING(bin.transItemsp->deleteTree(), bin.transItemsp);
        if (bin.transRepeatValueItemsp) {
            VL_DO_DANGLING(bin.transRepeatValueItemsp->deleteTree(), bin.transRepeatValueItemsp);
        }
        if (bin.withp) VL_DO_DANGLING(bin.withp->deleteTree(), bin.withp);
        if (bin.iffp) VL_DO_DANGLING(bin.iffp->deleteTree(), bin.iffp);
        if (bin.arraySizep) VL_DO_DANGLING(bin.arraySizep->deleteTree(), bin.arraySizep);
    }
    static void deleteCoverpointBinInfo(CoverpointBinInfo& bin) {
        if (bin.condp) VL_DO_DANGLING(bin.condp->deleteTree(), bin.condp);
        if (bin.valueItemsp) VL_DO_DANGLING(bin.valueItemsp->deleteTree(), bin.valueItemsp);
    }
    static void deleteCoverpointInfoBins(CoverpointInfo& info) {
        for (CoverpointBinInfo& bin : info.bins) deleteCoverpointBinInfo(bin);
        info.bins.clear();
    }
    static void eraseCoverpointInfo(std::vector<CoverpointInfo>& infos, const string& name) {
        infos.erase(std::remove_if(infos.begin(), infos.end(),
                                   [&](CoverpointInfo& info) {
                                       if (info.name != name) return false;
                                       deleteCoverpointInfoBins(info);
                                       return true;
                                   }),
                    infos.end());
    }
    static void clearPendingOptions(std::vector<CoverpointPendingOption>& options) {
        for (CoverpointPendingOption& opt : options) opt.valuep = nullptr;
        options.clear();
    }
    static void deleteCoverCrossBinSpec(CoverCrossBinSpec& bin) {
        if (bin.iffp) VL_DO_DANGLING(bin.iffp->deleteTree(), bin.iffp);
        for (CoverCrossClause& clause : bin.clauses) {
            if (clause.iffp) VL_DO_DANGLING(clause.iffp->deleteTree(), clause.iffp);
        }
    }
    AstNodeModule* currentModulep() const {
        AstNodeModule* lastp = nullptr;
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (!VN_IS(modp, Class)) lastp = modp;
        }
        return lastp;
    }
    AstClass* findClassByName(const string& name) const {
        AstClass* foundp = nullptr;
        v3Global.rootp()->foreach([&](AstClass* classp) {
            if (!foundp && classp->name() == name) foundp = classp;
        });
        return foundp;
    }
    AstVar* findVarByNameInNode(AstNode* scopep, const string& name) const {
        for (AstNode* nodep = scopep; nodep; nodep = nodep->nextp()) {
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->name() == name) return varp;
            }
        }
        return nullptr;
    }
    AstVar* findClassMemberVar(AstClass* classp, const string& name) const {
        if (!classp) return nullptr;
        for (AstNode* memberp = classp->membersp(); memberp; memberp = memberp->nextp()) {
            AstVar* const varp = VN_CAST(memberp, Var);
            if (varp && varp->name() == name) return varp;
        }
        return nullptr;
    }
    AstVar* findVisibleClassMemberVar(AstClass* classp, const string& name) const {
        for (AstClass* walkp = classp; walkp;
             walkp = walkp->extendsp() ? walkp->extendsp()->classp()
                                       : (walkp == currentClassDeclp() ? currentPendingClassBasep()
                                                                       : nullptr)) {
            if (AstVar* const varp = findClassMemberVar(walkp, name)) return varp;
        }
        return nullptr;
    }
    static bool nodeWithinScope(const AstNode* nodep, const AstNode* scopep) {
        for (const AstNode* backp = nodep; backp; backp = backp->backp()) {
            if (backp == scopep) return true;
        }
        return false;
    }
    AstVar* findCurrentClassMemberVar(const string& name) const {
        AstClass* const ownerClassp
            = m_covergroup.ownerClassp ? m_covergroup.ownerClassp : currentClassDeclp();
        if (!ownerClassp) return nullptr;
        if (AstVar* const memberp = findVisibleClassMemberVar(ownerClassp, name)) return memberp;
        for (auto it = m_declaredVars.rbegin(); it != m_declaredVars.rend(); ++it) {
            AstVar* const varp = *it;
            if (!varp || varp->isFuncLocal() || varp->name() != name) continue;
            if (m_covergroup.classp && nodeWithinScope(varp, m_covergroup.classp)) continue;
            if (m_covergroup.ctorp && nodeWithinScope(varp, m_covergroup.ctorp)) continue;
            if (m_covergroup.methods.sampleFuncp
                && nodeWithinScope(varp, m_covergroup.methods.sampleFuncp)) {
                continue;
            }
            return varp;
        }
        return nullptr;
    }
    static AstNodeDType* coverVarDTypep(AstVar* varp) {
        if (!varp) return nullptr;
        if (AstNodeDType* const dtypep = varp->subDTypep()) return dtypep;
        return varp->dtypep();
    }
    AstVar* findDeclaredCoverVarByName(const string& name) const {
        if (name.empty()) return nullptr;
        if (m_covergroup.active) {
            const auto it = m_covergroup.sampleVars.find(name);
            if (it != m_covergroup.sampleVars.end()) return it->second;
        }
        if (m_covergroup.methods.sampleFuncp) {
            if (AstVar* const varp = findVarByNameInNode(m_covergroup.methods.sampleFuncp->stmtsp(), name))
                return varp;
        }
        if (AstNodeModule* const modp = currentModulep()) {
            if (AstVar* const varp = findVarByNameInNode(modp->stmtsp(), name)) return varp;
        }
        AstVar* typedZeroWidthp = nullptr;
        AstVar* fallbackp = nullptr;
        for (auto it = m_declaredVars.rbegin(); it != m_declaredVars.rend(); ++it) {
            AstVar* const varp = *it;
            if (!varp || varp->isFuncLocal() || varp->isClassMember()) continue;
            if (varp->name() != name) continue;
            if (AstNodeDType* const dtypep = coverVarDTypep(varp)) {
                const AstNodeDType* const skipDtp = dtypep->skipRefp();
                if (skipDtp && !skipDtp->generic() && skipDtp->width() > 0) {
                    return varp;
                }
                if (skipDtp && !skipDtp->generic() && !typedZeroWidthp) typedZeroWidthp = varp;
            }
            if (!fallbackp) fallbackp = varp;
        }
        return typedZeroWidthp ? typedZeroWidthp : fallbackp;
    }
    bool hasVarInNodeList(AstNode* scopep, const AstVar* varp) const {
        for (AstNode* nodep = scopep; nodep; nodep = nodep->nextp()) {
            if (nodep == varp) return true;
        }
        return false;
    }
    void addSampleVarDecl(AstVar* varp) {
        AstNode* const firstp = m_covergroup.methods.sampleFuncp->stmtsp();
        for (AstNode* nodep = firstp; nodep; nodep = nodep->nextp()) {
            if (!VN_IS(nodep, Var)) {
                nodep->addHereThisAsNext(varp);
                return;
            }
        }
        m_covergroup.methods.sampleFuncp->addStmtsp(varp);
    }
    AstVar* resolveDirectCoverVar(AstNodeExpr* exprp) const {
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            AstVar* const varp = refp->varp();
            if (varp && varp->isClassMember() && !varp->isFuncLocal()) {
                if (m_covergroup.classp && findClassMemberVar(m_covergroup.classp, varp->name()) == varp) {
                    return varp;
                }
                return nullptr;
            }
            return varp;
        }
        const AstParseRef* const parseRefp = VN_CAST(exprp, ParseRef);
        if (!parseRefp) return nullptr;
        return findDeclaredCoverVarByName(parseRefp->name());
    }
    AstVar* resolveSimpleCoverVar(AstNodeExpr* exprp) const {
        AstVar* const varp = resolveDirectCoverVar(exprp);
        if (!varp) return nullptr;
        if (m_covergroup.methods.sampleFuncp
            && hasVarInNodeList(m_covergroup.methods.sampleFuncp->stmtsp(), varp)) {
            return varp;
        }
        if (AstNodeModule* const modp = currentModulep()) {
            if (hasVarInNodeList(modp->stmtsp(), varp)) return varp;
        }
        if (m_covergroup.classp && findClassMemberVar(m_covergroup.classp, varp->name()) == varp) {
            return varp;
        }
        return nullptr;
    }
    static const AstArg* cloneCovergroupImplicitSampleArgs(const AstNodeDType* dtypep) {
        return singletonp()->findCovergroupImplicitSampleArgs(dtypep);
    }
    static const AstArg* cloneCovergroupImplicitSampleArgs(const string& name) {
        return singletonp()->findCovergroupImplicitSampleArgs(name);
    }
    static string tailClassName(AstNode* nodep) {
        if (const AstParseRef* const refp = VN_CAST(nodep, ParseRef)) return refp->name();
        if (const AstDot* const dotp = VN_CAST(nodep, Dot)) return tailClassName(dotp->rhsp());
        return "";
    }
    AstClass* currentPendingClassBasep() const {
        if (m_pendingClassExtendsStack.empty()) return nullptr;
        AstClassExtends* const extp = m_pendingClassExtendsStack.back();
        if (!extp) return nullptr;
        if (AstClass* const classp = extp->classOrNullp()) return classp;
        return findClassByName(tailClassName(extp->classOrPkgsp()));
    }
    void enterClassDecl(AstClass* classp) {
        ++m_classDepth;
        m_classStack.push_back(classp);
        m_pendingClassExtendsStack.push_back(nullptr);
    }
    void leaveClassDecl() {
        if (m_classDepth > 0) --m_classDepth;
        if (!m_classStack.empty()) m_classStack.pop_back();
        if (!m_pendingClassExtendsStack.empty()) m_pendingClassExtendsStack.pop_back();
    }
    bool insideClassDecl() const { return m_classDepth > 0; }
    AstClass* currentClassDeclp() const { return m_classStack.empty() ? nullptr : m_classStack.back(); }
    void markCovergroupUnsupportedExtends() { m_covergroup.extendsUnsupported = true; }
    void renameCovergroupAutosample(const string& oldName, const string& newName) {
        const auto it = m_covergroupAutoSamples.find(oldName);
        if (it == m_covergroupAutoSamples.end()) return;
        m_covergroupAutoSamples.emplace(newName, std::move(it->second));
        m_covergroupAutoSamples.erase(it);
    }
    static string unscopedName(const string& name) {
        size_t pos = name.rfind("::");
        if (pos != string::npos) return name.substr(pos + 2);
        pos = name.rfind('.');
        if (pos != string::npos) return name.substr(pos + 1);
        return name;
    }
    const CovergroupAutoSample* findCovergroupAutosample(const AstNodeDType* dtypep) const {
        if (!dtypep) return nullptr;
        std::vector<string> names;
        const auto addDTypeNames = [&](const AstNodeDType* dtp) {
            if (!dtp) return;
            if (const AstRefDType* const refp = VN_CAST(dtp, RefDType)) {
                names.push_back(refp->name());
                names.push_back(unscopedName(refp->name()));
            } else if (const AstClassRefDType* const classRefp = VN_CAST(dtp, ClassRefDType)) {
                names.push_back(classRefp->name());
                names.push_back(unscopedName(classRefp->name()));
            }
        };
        addDTypeNames(dtypep);
        addDTypeNames(dtypep->getChildDTypep());
        for (const string& name : names) {
            if (name.empty()) continue;
            const auto it = m_covergroupAutoSamples.find(name);
            if (it != m_covergroupAutoSamples.end()) return &it->second;
        }
        return nullptr;
    }
    const AstArg* findCovergroupImplicitSampleArgs(const AstNodeDType* dtypep) const {
        if (!dtypep) return nullptr;
        std::vector<string> names;
        const auto addDTypeNames = [&](const AstNodeDType* dtp) {
            if (!dtp) return;
            if (const AstRefDType* const refp = VN_CAST(dtp, RefDType)) {
                names.push_back(refp->name());
                names.push_back(unscopedName(refp->name()));
            } else if (const AstClassRefDType* const classRefp = VN_CAST(dtp, ClassRefDType)) {
                names.push_back(classRefp->name());
                names.push_back(unscopedName(classRefp->name()));
            }
        };
        addDTypeNames(dtypep);
        addDTypeNames(dtypep->getChildDTypep());
        for (const string& name : names) {
            if (name.empty()) continue;
            const auto it = m_covergroupImplicitSampleArgs.find(name);
            if (it != m_covergroupImplicitSampleArgs.end()) return it->second;
        }
        return nullptr;
    }
    const AstArg* findCovergroupImplicitSampleArgs(const string& name) const {
        if (name.empty()) return nullptr;
        const auto it = m_covergroupImplicitSampleArgs.find(name);
        if (it != m_covergroupImplicitSampleArgs.end()) return it->second;
        const string shortName = unscopedName(name);
        const auto shortIt = m_covergroupImplicitSampleArgs.find(shortName);
        return shortIt != m_covergroupImplicitSampleArgs.end() ? shortIt->second : nullptr;
    }
    bool makeCovergroupAtAtSampleStmtImpl(AstVar* varp,
                                          std::vector<std::pair<std::string, bool>>& hooks,
                                          AstNode*& stmtp) const {
        hooks.clear();
        stmtp = nullptr;
        if (!varp) return false;
        std::vector<string> names;
        const AstNodeDType* const directp = varp->dtypep() ? varp->dtypep() : varp->getChildDTypep();
        if (const AstRefDType* const refp = VN_CAST(directp, RefDType)) {
            names.push_back(refp->name());
            names.push_back(unscopedName(refp->name()));
        } else if (const AstClassRefDType* const classRefp = VN_CAST(directp, ClassRefDType)) {
            names.push_back(classRefp->name());
            names.push_back(unscopedName(classRefp->name()));
        } else if (const AstRefDType* const refp = VN_CAST(varp->getChildDTypep(), RefDType)) {
            names.push_back(refp->name());
            names.push_back(unscopedName(refp->name()));
        } else if (const AstClassRefDType* const classRefp
                   = VN_CAST(varp->getChildDTypep(), ClassRefDType)) {
            names.push_back(classRefp->name());
            names.push_back(unscopedName(classRefp->name()));
        }
        const CovergroupAutoSample* autosp = nullptr;
        for (const string& name : names) {
            const auto it = m_covergroupAutoSamples.find(name);
            if (it != m_covergroupAutoSamples.end()) {
                autosp = &it->second;
                break;
            }
        }
        if (autosp && !autosp->atatHooks.empty()) {
            AstMethodCall* const samplep = new AstMethodCall{
                varp->fileline(), new AstVarRef{varp->fileline(), varp, VAccess::READ}, "sample",
                autosp->argsp ? static_cast<::AstArg*>(autosp->argsp->cloneTree(true)) : nullptr};
            if (autosp->sampleFuncp) samplep->taskp(autosp->sampleFuncp);
            samplep->dtypeSetVoid();
            stmtp = new AstIf{
                varp->fileline(),
                new AstNeq{varp->fileline(), new AstVarRef{varp->fileline(), varp, VAccess::READ},
                           new AstConst{varp->fileline(), AstConst::Null{}}},
                samplep->makeStmt()};
            for (const CovergroupState::AtAtHook& hook : autosp->atatHooks) {
                hooks.emplace_back(hook.target, hook.begin);
            }
            return true;
        }

        AstClass* classp = nullptr;
        if (const AstClassRefDType* const classRefp = VN_CAST(directp, ClassRefDType)) {
            classp = classRefp->classp();
            if (!classp) classp = findClassByName(unscopedName(classRefp->name()));
        } else if (const AstRefDType* const refp = VN_CAST(directp, RefDType)) {
            classp = findClassByName(refp->name());
            if (!classp) classp = findClassByName(unscopedName(refp->name()));
        } else if (const AstClassRefDType* const classRefp
                   = VN_CAST(varp->getChildDTypep(), ClassRefDType)) {
            classp = classRefp->classp();
            if (!classp) classp = findClassByName(unscopedName(classRefp->name()));
        } else if (const AstRefDType* const refp = VN_CAST(varp->getChildDTypep(), RefDType)) {
            classp = findClassByName(refp->name());
            if (!classp) classp = findClassByName(unscopedName(refp->name()));
        }
        if (!classp) return false;
        for (AstNode* memberp = classp->membersp(); memberp; memberp = memberp->nextp()) {
            AstVar* const cgVarp = VN_CAST(memberp, Var);
            if (!cgVarp) continue;
            const CovergroupAutoSample* const cgAutosp = findCovergroupAutosample(cgVarp->dtypep());
            if (!cgAutosp || cgAutosp->atatHooks.empty()) continue;
            AstNodeExpr* const objRefp = new AstVarRef{varp->fileline(), varp, VAccess::READ};
            AstMemberSel* const cgCallRefp
                = new AstMemberSel{varp->fileline(), objRefp->cloneTreePure(false), cgVarp};
            cgCallRefp->access(VAccess::READ);
            ::AstArg* argsp
                = cgAutosp->argsp ? static_cast<::AstArg*>(cgAutosp->argsp->cloneTree(true)) : nullptr;
            if (argsp) qualifyClassMemberRefs(argsp, objRefp->cloneTreePure(false), classp);
            AstMethodCall* const samplep
                = new AstMethodCall{varp->fileline(), cgCallRefp, "sample", argsp};
            if (cgAutosp->sampleFuncp) samplep->taskp(cgAutosp->sampleFuncp);
            samplep->dtypeSetVoid();
            AstNodeExpr* const objValidp
                = new AstNeq{varp->fileline(), objRefp->cloneTreePure(false),
                             new AstConst{varp->fileline(), AstConst::Null{}}};
            AstMemberSel* const cgCondRefp
                = new AstMemberSel{varp->fileline(), objRefp->cloneTreePure(false), cgVarp};
            cgCondRefp->access(VAccess::READ);
            AstNodeExpr* const cgValidp
                = new AstNeq{varp->fileline(), cgCondRefp,
                             new AstConst{varp->fileline(), AstConst::Null{}}};
            stmtp = new AstIf{varp->fileline(),
                              makeCoverLogAnd(varp->fileline(), objValidp, cgValidp),
                              samplep->makeStmt()};
            for (const CovergroupState::AtAtHook& hook : cgAutosp->atatHooks) {
                hooks.emplace_back(hook.target, hook.begin);
            }
            return true;
        }
        return false;
    }
    static AstNodeExpr* suppressGeneratedCoverageCondWarns(AstNodeExpr* exprp) {
        if (!exprp) return nullptr;
        exprp->fileline()->warnOff(V3ErrorCode::WIDTHTRUNC, true);
        exprp->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
        return exprp;
    }
    static AstNodeExpr* makeCoverLogAnd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        return suppressGeneratedCoverageCondWarns(new AstLogAnd{fl, lhsp, rhsp});
    }
    static AstNodeExpr* makeCoverLogNot(FileLine* fl, AstNodeExpr* exprp) {
        return suppressGeneratedCoverageCondWarns(new AstLogNot{fl, exprp});
    }
    static AstNodeExpr* makeCoverLogOr(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        return suppressGeneratedCoverageCondWarns(new AstLogOr{fl, lhsp, rhsp});
    }
    static AstSenItem* makeCovergroupAtAtEvent(FileLine* fl, bool begin, AstNodeExpr* targetp) {
        return new AstSenItem{
            fl, VEdgeType::ET_TRUE,
            new AstTaggedExpr{fl, begin ? V3CoverAtat::kTagBegin : V3CoverAtat::kTagEnd, targetp}};
    }
    AstNode* qualifyClassMemberRefs(AstNode* treep, AstNodeExpr* objRefp, AstClass* classp) const {
        if (!treep || !objRefp || !classp) return treep;
        std::vector<AstParseRef*> parseRefs;
        treep->foreach([&](AstParseRef* refp) {
            if (!refp->lhsp() && findVisibleClassMemberVar(classp, refp->name())) {
                parseRefs.push_back(refp);
            }
        });
        for (AstParseRef* const refp : parseRefs) {
            AstVar* const varp = findVisibleClassMemberVar(classp, refp->name());
            if (!varp) continue;
            AstMemberSel* const selp
                = new AstMemberSel{refp->fileline(), objRefp->cloneTreePure(false), varp};
            selp->access(VAccess::READ);
            refp->replaceWith(selp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        std::vector<AstVarRef*> varRefs;
        treep->foreach([&](AstVarRef* refp) {
            if (refp->varp() && refp->varp()->isClassMember() && !refp->varp()->isFuncLocal()) {
                varRefs.push_back(refp);
            }
        });
        for (AstVarRef* const refp : varRefs) {
            AstMemberSel* const selp
                = new AstMemberSel{refp->fileline(), objRefp->cloneTreePure(false), refp->varp()};
            selp->access(refp->access());
            refp->replaceWith(selp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        return treep;
    }
    std::string defaultCoverpointName(AstNodeExpr* exprp) const {
        if (const AstVarRef* const refp = VN_CAST(exprp, VarRef)) return refp->varp()->name();
        if (AstVar* const varp = resolveSimpleCoverVar(exprp)) return varp->name();
        if (const AstParseRef* const parseRefp = VN_CAST(exprp, ParseRef)) return parseRefp->name();
        return "";
    }
    AstNodeDType* cloneCoverExprDType(FileLine* fl, const AstNodeDType* srcp) const {
        AstNode* const anchorp = m_covergroup.methods.sampleFuncp
                                     ? static_cast<AstNode*>(m_covergroup.methods.sampleFuncp)
                                     : static_cast<AstNode*>(v3Global.rootp());
        if (!srcp) return anchorp->findIntDType();
        const AstNodeDType* const basep = srcp->skipRefp();
        if (const AstBasicDType* const basicp = VN_CAST(basep, BasicDType)) {
            if (basicp->isBitLogic()) {
                return anchorp->findBitOrLogicDType(basicp->width(), basicp->widthMin(),
                                                    basicp->numeric(), basicp->isFourstate());
            }
            return anchorp->findBasicDType(basicp->keyword());
        }
        if (const AstEnumDType* const enump = VN_CAST(srcp->skipRefToEnump(), EnumDType)) {
            const AstBasicDType* const basicp
                = enump->subDTypep() ? VN_CAST(enump->subDTypep()->skipRefp(), BasicDType) : nullptr;
            if (basicp) {
                if (basicp->isBitLogic()) {
                    return anchorp->findBitOrLogicDType(basicp->width(), basicp->widthMin(),
                                                        basicp->numeric(), basicp->isFourstate());
                }
                return anchorp->findBasicDType(basicp->keyword());
            }
            return anchorp->findIntDType();
        }
        return const_cast<AstNodeDType*>(srcp)->cloneTreePure(false);
    }
    const AstNodeDType* coverExprSourceDTypep(AstNodeExpr* exprp) const {
        if (AstVar* const varp = resolveDirectCoverVar(exprp)) return coverVarDTypep(varp);
        return exprp ? exprp->dtypep() : nullptr;
    }
    const AstNodeDType* hiddenOwnerCoverDTypep(AstVar* ownerVarp) const {
        const AstNodeDType* dtypep = ownerVarp ? coverVarDTypep(ownerVarp) : nullptr;
        if (const AstDefImplicitDType* const implicitp = VN_CAST(dtypep, DefImplicitDType)) {
            dtypep = implicitp->subDTypep() ? implicitp->subDTypep() : dtypep;
        }
        if (const AstEnumDType* const enump = VN_CAST(dtypep, EnumDType)) {
            dtypep = enump->subDTypep() ? enump->subDTypep() : dtypep;
        } else if (const AstEnumDType* const enump = dtypep ? VN_CAST(dtypep->skipRefToEnump(), EnumDType) : nullptr) {
            dtypep = enump->subDTypep() ? enump->subDTypep() : dtypep;
        }
        return dtypep;
    }
    AstNodeDType* inferCoverExprDType(FileLine* fl, AstNodeExpr* exprp) const {
        if (AstVar* const varp = resolveDirectCoverVar(exprp)) {
            return cloneCoverExprDType(fl, coverVarDTypep(varp));
        }
        if (exprp && exprp->dtypep()) return cloneCoverExprDType(fl, exprp->dtypep());
        return cloneCoverExprDType(fl, nullptr);
    }
    AstConst* makeCoverDefaultConst(FileLine* fl, const AstNodeDType* dtypep) const {
        const AstNodeDType* const basep = dtypep ? dtypep->skipRefp() : nullptr;
        const int width = (basep && !basep->generic() && basep->width() > 0) ? basep->width() : 1;
        return new AstConst{fl, AstConst::WidthedValue{}, width, 0};
    }
    AstVarRef* addHiddenCoverSampleArg(FileLine* fl, const string& prefix, AstNodeExpr* actualExprp,
                                       const AstNodeDType* srcDTypep = nullptr,
                                       AstNodeExpr* defaultp = nullptr) {
        AstNodeDType* const dtypep
            = srcDTypep ? cloneCoverExprDType(fl, srcDTypep) : inferCoverExprDType(fl, actualExprp);
        AstVar* const varp
            = new AstVar{fl, VVarType::MEMBER,
                         "verilator_cov_" + prefix + cvtToStr(m_covergroup.hiddenSampleArgNum++),
                         dtypep};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        varp->funcLocal(true);
        varp->direction(VDirection::INPUT);
        if (defaultp) varp->valuep(defaultp);
        addSampleVarDecl(varp);
        if (actualExprp) actualExprp->dtypep(nullptr);
        m_covergroup.autoSampleArgsp
            = AstNode::addNextNull(m_covergroup.autoSampleArgsp, new AstArg{fl, "", actualExprp});
        return new AstVarRef{fl, varp, VAccess::READ};
    }
    AstVar* createStoredCtorCoverVar(AstVar* ctorVarp) {
        if (!ctorVarp) return nullptr;
        const auto it = m_covergroup.ctorBoundVars.find(ctorVarp->name());
        if (it != m_covergroup.ctorBoundVars.end()) return it->second;
        const AstNodeDType* const ctorDTypep
            = ctorVarp->dtypep() ? ctorVarp->dtypep() : coverVarDTypep(ctorVarp);
        AstNodeDType* const dtypep = cloneCoverExprDType(ctorVarp->fileline(), ctorDTypep);
        AstVar* const memberp = new AstVar{ctorVarp->fileline(), VVarType::MEMBER,
                                           "verilator_cov_ctor_" + ctorVarp->name(), dtypep};
        memberp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_covergroup.classp->addMembersp(memberp);
        AstAssign* const assignp = new AstAssign{
            ctorVarp->fileline(), new AstVarRef{ctorVarp->fileline(), memberp, VAccess::WRITE},
            new AstVarRef{ctorVarp->fileline(), ctorVarp, VAccess::READ}};
        assignp->fileline()->warnOff(V3ErrorCode::WIDTHTRUNC, true);
        assignp->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
        m_covergroup.ctorp->addStmtsp(assignp);
        m_covergroup.ctorBoundVars.emplace(ctorVarp->name(), memberp);
        return memberp;
    }
    void prepareCovergroupCtorBindings() {
        for (AstNode* stmtp = m_covergroup.ctorp ? m_covergroup.ctorp->stmtsp() : nullptr; stmtp;
             stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp || !varp->isIO()) continue;
            createStoredCtorCoverVar(varp);
        }
    }
    AstNode* bindNonEventCovergroupRefs(AstNode* treep) {
        if (!treep || m_covergroup.eventDriven) return treep;
        if (AstParseRef* const refp = VN_CAST(treep, ParseRef)) {
            const auto ctorIt = m_covergroup.ctorBoundVars.find(refp->name());
            if (ctorIt != m_covergroup.ctorBoundVars.end()) {
                treep = new AstVarRef{refp->fileline(), ctorIt->second, VAccess::READ};
                VL_DO_DANGLING(refp->deleteTree(), refp);
                return treep;
            }
            AstVar* const ownerVarp = findCurrentClassMemberVar(refp->name());
            if (ownerVarp && !ownerVarp->isFuncLocal()) {
                treep = addHiddenCoverSampleArg(
                    refp->fileline(), "cg_owner_" + ownerVarp->name() + "__",
                    new AstParseRef{refp->fileline(), refp->name()},
                    hiddenOwnerCoverDTypep(ownerVarp),
                    makeCoverDefaultConst(refp->fileline(), hiddenOwnerCoverDTypep(ownerVarp)));
                VL_DO_DANGLING(refp->deleteTree(), refp);
                return treep;
            }
        } else if (AstVarRef* const refp = VN_CAST(treep, VarRef)) {
            AstVar* const ownerVarp = refp->varp() ? findCurrentClassMemberVar(refp->varp()->name()) : nullptr;
            if (ownerVarp && !ownerVarp->isFuncLocal()) {
                treep = addHiddenCoverSampleArg(
                    refp->fileline(), "cg_owner_" + ownerVarp->name() + "__",
                    new AstParseRef{refp->fileline(), ownerVarp->name()}, hiddenOwnerCoverDTypep(ownerVarp),
                    makeCoverDefaultConst(refp->fileline(), hiddenOwnerCoverDTypep(ownerVarp)));
                VL_DO_DANGLING(refp->deleteTree(), refp);
                return treep;
            }
        }
        std::vector<AstParseRef*> parseRefs;
        treep->foreach([&](AstParseRef* refp) {
            if (!refp->lhsp() && !refp->ftaskrefp()) parseRefs.push_back(refp);
        });
        for (AstParseRef* const refp : parseRefs) {
            const auto ctorIt = m_covergroup.ctorBoundVars.find(refp->name());
            if (ctorIt != m_covergroup.ctorBoundVars.end()) {
                AstVar* const boundVarp = ctorIt->second;
                AstVarRef* const newp = new AstVarRef{refp->fileline(), boundVarp, VAccess::READ};
                refp->replaceWith(newp);
                VL_DO_DANGLING(refp->deleteTree(), refp);
                continue;
            }
            AstVar* const ownerVarp = findCurrentClassMemberVar(refp->name());
            if (!ownerVarp || ownerVarp->isFuncLocal()) continue;
            AstVarRef* const newp = addHiddenCoverSampleArg(
                refp->fileline(), "cg_owner_" + ownerVarp->name() + "__",
                new AstParseRef{refp->fileline(), refp->name()},
                hiddenOwnerCoverDTypep(ownerVarp),
                makeCoverDefaultConst(refp->fileline(), hiddenOwnerCoverDTypep(ownerVarp)));
            refp->replaceWith(newp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        std::vector<AstVarRef*> varRefs;
        treep->foreach([&](AstVarRef* refp) {
            AstVar* const ownerVarp = refp->varp() ? findCurrentClassMemberVar(refp->varp()->name()) : nullptr;
            if (ownerVarp && !ownerVarp->isFuncLocal()) {
                varRefs.push_back(refp);
            }
        });
        for (AstVarRef* const refp : varRefs) {
            AstVar* const ownerVarp = findCurrentClassMemberVar(refp->varp()->name());
            AstVarRef* const newp = addHiddenCoverSampleArg(
                refp->fileline(), "cg_owner_" + ownerVarp->name() + "__",
                new AstParseRef{refp->fileline(), ownerVarp->name()}, hiddenOwnerCoverDTypep(ownerVarp),
                makeCoverDefaultConst(refp->fileline(), hiddenOwnerCoverDTypep(ownerVarp)));
            refp->replaceWith(newp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        return treep;
    }
    void enableCovergroupEventSampling(AstNode* coverageEventp) {
        if (!coverageEventp) return;
        if (AstSenItem* const senItemp = VN_CAST(coverageEventp, SenItem)) {
            m_covergroup.eventDriven = true;
            bool isAtAt = true;
            for (AstSenItem* itemp = senItemp; itemp; itemp = VN_AS(itemp->nextp(), SenItem)) {
                const AstTaggedExpr* const taggedp = VN_CAST(itemp->sensp(), TaggedExpr);
                const AstParseRef* const refp = taggedp ? VN_CAST(taggedp->exprp(), ParseRef) : nullptr;
                if (!taggedp || !refp || refp->lhsp() || refp->ftaskrefp()) {
                    isAtAt = false;
                    break;
                }
            }
            if (isAtAt) {
                for (AstSenItem* itemp = senItemp; itemp; itemp = VN_AS(itemp->nextp(), SenItem)) {
                    const AstTaggedExpr* const taggedp = VN_AS(itemp->sensp(), TaggedExpr);
                    const AstParseRef* const refp = VN_AS(taggedp->exprp(), ParseRef);
                    m_covergroup.atatHooks.push_back(CovergroupState::AtAtHook{
                        taggedp->name() == V3CoverAtat::kTagBegin, refp->name()});
                }
            } else {
                m_covergroup.eventSenTreep = new ::AstSenTree{senItemp->fileline(), senItemp};
            }
            return;
        }
        for (AstNode* argp = coverageEventp; argp; argp = argp->nextp()) {
            if (AstVar* const varp = VN_CAST(argp, Var)) m_covergroup.sampleVars[varp->name()] = varp;
        }
        m_covergroup.methods.sampleFuncp->addStmtsp(coverageEventp);
    }
    int optionConstInt(const std::vector<CoverpointPendingOption>& options, const string& member,
                       int defaultValue) const {
        for (auto it = options.rbegin(); it != options.rend(); ++it) {
            if (it->typeOption) continue;
            if (it->member != member) continue;
            if (const AstConst* const constp = VN_CAST(it->valuep, Const)) return constp->toSInt();
        }
        return defaultValue;
    }
    bool constExprToSInt(AstNodeExpr* exprp, int32_t& value) const {
        if (const AstConst* const constp = VN_CAST(exprp, Const)) {
            value = constp->toSInt();
            return true;
        }
        if (const AstCast* const castp = VN_CAST(exprp, Cast)) {
            return constExprToSInt(castp->fromp(), value);
        }
        if (const AstCastSize* const castp = VN_CAST(exprp, CastSize)) {
            return constExprToSInt(castp->lhsp(), value);
        }
        if (const AstExtend* const extp = VN_CAST(exprp, Extend)) {
            return constExprToSInt(extp->lhsp(), value);
        }
        if (const AstExtendS* const extp = VN_CAST(exprp, ExtendS)) {
            return constExprToSInt(extp->lhsp(), value);
        }
        if (const AstSigned* const signedp = VN_CAST(exprp, Signed)) {
            return constExprToSInt(signedp->lhsp(), value);
        }
        if (const AstUnsigned* const unsignedp = VN_CAST(exprp, Unsigned)) {
            return constExprToSInt(unsignedp->lhsp(), value);
        }
        if (const AstNegate* const negp = VN_CAST(exprp, Negate)) {
            int32_t rhs = 0;
            if (!constExprToSInt(negp->lhsp(), rhs)) return false;
            value = -rhs;
            return true;
        }
        if (const AstAdd* const addp = VN_CAST(exprp, Add)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(addp->lhsp(), lhs) || !constExprToSInt(addp->rhsp(), rhs)) return false;
            value = lhs + rhs;
            return true;
        }
        if (const AstSub* const subp = VN_CAST(exprp, Sub)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(subp->lhsp(), lhs) || !constExprToSInt(subp->rhsp(), rhs)) return false;
            value = lhs - rhs;
            return true;
        }
        if (const AstMul* const mulp = VN_CAST(exprp, Mul)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(mulp->lhsp(), lhs) || !constExprToSInt(mulp->rhsp(), rhs)) return false;
            value = lhs * rhs;
            return true;
        }
        if (const AstDiv* const divp = VN_CAST(exprp, Div)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(divp->lhsp(), lhs) || !constExprToSInt(divp->rhsp(), rhs) || rhs == 0) {
                return false;
            }
            value = lhs / rhs;
            return true;
        }
        if (const AstDivS* const divp = VN_CAST(exprp, DivS)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(divp->lhsp(), lhs) || !constExprToSInt(divp->rhsp(), rhs) || rhs == 0) {
                return false;
            }
            value = lhs / rhs;
            return true;
        }
        if (const AstModDiv* const modp = VN_CAST(exprp, ModDiv)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(modp->lhsp(), lhs) || !constExprToSInt(modp->rhsp(), rhs) || rhs == 0) {
                return false;
            }
            value = lhs % rhs;
            return true;
        }
        if (const AstModDivS* const modp = VN_CAST(exprp, ModDivS)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(modp->lhsp(), lhs) || !constExprToSInt(modp->rhsp(), rhs) || rhs == 0) {
                return false;
            }
            value = lhs % rhs;
            return true;
        }
        if (const AstEq* const eqp = VN_CAST(exprp, Eq)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(eqp->lhsp(), lhs) || !constExprToSInt(eqp->rhsp(), rhs)) return false;
            value = (lhs == rhs);
            return true;
        }
        if (const AstNeq* const neqp = VN_CAST(exprp, Neq)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(neqp->lhsp(), lhs) || !constExprToSInt(neqp->rhsp(), rhs)) return false;
            value = (lhs != rhs);
            return true;
        }
        if (const AstLt* const ltp = VN_CAST(exprp, Lt)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(ltp->lhsp(), lhs) || !constExprToSInt(ltp->rhsp(), rhs)) return false;
            value = (lhs < rhs);
            return true;
        }
        if (const AstLte* const ltep = VN_CAST(exprp, Lte)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(ltep->lhsp(), lhs) || !constExprToSInt(ltep->rhsp(), rhs)) return false;
            value = (lhs <= rhs);
            return true;
        }
        if (const AstGt* const gtp = VN_CAST(exprp, Gt)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(gtp->lhsp(), lhs) || !constExprToSInt(gtp->rhsp(), rhs)) return false;
            value = (lhs > rhs);
            return true;
        }
        if (const AstGte* const gtep = VN_CAST(exprp, Gte)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(gtep->lhsp(), lhs) || !constExprToSInt(gtep->rhsp(), rhs)) return false;
            value = (lhs >= rhs);
            return true;
        }
        if (const AstLogAnd* const andp = VN_CAST(exprp, LogAnd)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(andp->lhsp(), lhs) || !constExprToSInt(andp->rhsp(), rhs)) return false;
            value = (lhs && rhs);
            return true;
        }
        if (const AstLogOr* const orp = VN_CAST(exprp, LogOr)) {
            int32_t lhs = 0;
            int32_t rhs = 0;
            if (!constExprToSInt(orp->lhsp(), lhs) || !constExprToSInt(orp->rhsp(), rhs)) return false;
            value = (lhs || rhs);
            return true;
        }
        if (const AstNot* const notp = VN_CAST(exprp, Not)) {
            int32_t rhs = 0;
            if (!constExprToSInt(notp->lhsp(), rhs)) return false;
            value = !rhs;
            return true;
        }
        return false;
    }
    bool constRangeEndpoints(AstNodeExpr* exprp, int32_t& lo, int32_t& hi) const {
        if (AstInsideRange* const rangep = VN_CAST(exprp, InsideRange)) {
            return constExprToSInt(rangep->lhsp(), lo) && constExprToSInt(rangep->rhsp(), hi);
        }
        if (constExprToSInt(exprp, lo)) {
            hi = lo;
            return true;
        }
        return false;
    }
    AstNodeExpr* newIntConst(FileLine* fl, int32_t value) const {
        return new AstConst{fl, AstConst::Signed32{}, value};
    }
    AstNodeExpr* newCoverExprConstForDType(FileLine* fl, const AstNodeDType* dtypep,
                                           int32_t value) const {
        const AstNodeDType* const skipDtp = dtypep ? dtypep->skipRefp() : nullptr;
        if (const AstBasicDType* const basicp = VN_CAST(skipDtp, BasicDType)) {
            if (basicp->isBitLogic()) {
                int width = basicp->width();
                if (basicp->isRanged()) width = std::abs(basicp->left() - basicp->right()) + 1;
                V3Number num{fl, std::max(1, width), static_cast<uint32_t>(value)};
                num.isSigned(basicp->isSigned());
                return new AstConst{fl, num};
            }
        }
        return newIntConst(fl, value);
    }
    AstNodeExpr* newCoverExprConst(FileLine* fl, int32_t value) const {
        return newCoverExprConstForDType(fl, coverExprSourceDTypep(m_coverpoint.exprp), value);
    }
    AstNodeExpr* newRangeExprForDType(FileLine* fl, const AstNodeDType* dtypep, int32_t lo,
                                      int32_t hi) const {
        if (lo == hi) return newCoverExprConstForDType(fl, dtypep, lo);
        return new AstInsideRange{fl, newCoverExprConstForDType(fl, dtypep, lo),
                                  newCoverExprConstForDType(fl, dtypep, hi)};
    }
    AstNodeExpr* newRangeExpr(FileLine* fl, int32_t lo, int32_t hi) const {
        if (lo == hi) return newCoverExprConst(fl, lo);
        return new AstInsideRange{fl, newCoverExprConst(fl, lo), newCoverExprConst(fl, hi)};
    }
    bool collectConstIntervals(AstNodeExpr* itemsp,
                               std::vector<std::pair<int32_t, int32_t>>& intervals) const {
        for (AstNodeExpr* itemp = itemsp; itemp; itemp = VN_AS(itemp->nextp(), NodeExpr)) {
            int32_t lo = 0;
            int32_t hi = 0;
            if (!constRangeEndpoints(itemp, lo, hi)) return false;
            if (hi < lo) std::swap(lo, hi);
            intervals.emplace_back(lo, hi);
        }
        return !intervals.empty();
    }
    bool wildcardValueItemsSupported(AstNodeExpr* itemsp) const {
        for (AstNodeExpr* itemp = itemsp; itemp; itemp = VN_AS(itemp->nextp(), NodeExpr)) {
            if (VN_IS(itemp, InsideRange)) return false;
        }
        return true;
    }
    AstNodeExpr* newValueItemListFromIntervals(
        FileLine* fl, const std::vector<std::pair<int32_t, int32_t>>& intervals) const {
        AstNodeExpr* itemsp = nullptr;
        for (const auto& interval : intervals) {
            AstNodeExpr* const itemp = newRangeExpr(fl, interval.first, interval.second);
            itemsp = itemsp ? AstNode::addNextNull<AstNodeExpr, AstNodeExpr>(itemsp, itemp) : itemp;
        }
        return itemsp;
    }
    bool coverExprDiscreteDomain(AstNodeExpr* exprp, int autoBinMax, int32_t& lo, int32_t& hi) const {
        if (AstVar* const varp = resolveDirectCoverVar(exprp)) {
            const AstNodeDType* const skipDtp
                = coverVarDTypep(varp) ? coverVarDTypep(varp)->skipRefp() : nullptr;
            if (const AstBasicDType* const basicp = VN_CAST(skipDtp, BasicDType)) {
                if (basicp->isBitLogic() && basicp->isRanged()) {
                    const int left = basicp->left();
                    const int right = basicp->right();
                    const int width = std::abs(left - right) + 1;
                    const bool isSigned = basicp->isSigned();
                    if (!isSigned && width <= 30
                        && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
                        lo = 0;
                        hi = (1u << width) - 1;
                        return true;
                    }
                    if (isSigned && width > 0 && width <= 16
                        && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
                        lo = -(1 << (width - 1));
                        hi = (1 << (width - 1)) - 1;
                        return true;
                    }
                }
            }
        }
        AstNodeDType* const dtypep = inferCoverExprDType(exprp ? exprp->fileline() : nullptr, exprp);
        AstNodeDType* const skipDtp = dtypep ? dtypep->skipRefp() : nullptr;
        const int width = skipDtp ? skipDtp->width() : 32;
        const bool isSigned = skipDtp ? skipDtp->isSigned() : true;
        if (dtypep && !dtypep->generic()) VL_DO_DANGLING(dtypep->deleteTree(), dtypep);
        if (width <= 0) return false;
        if (!isSigned && width <= 30 && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
            lo = 0;
            hi = (1u << width) - 1;
            return true;
        }
        if (isSigned && width > 0 && width <= 16 && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
            lo = -(1 << (width - 1));
            hi = (1 << (width - 1)) - 1;
            return true;
        }
        if (width == 1) {
            lo = isSigned ? -1 : 0;
            hi = 1;
            return true;
        }
        if (width > 31) {
            lo = std::numeric_limits<int32_t>::min();
            hi = std::numeric_limits<int32_t>::max();
            return true;
        }
        if (isSigned) {
            lo = -(1 << (width - 1));
            hi = (1 << (width - 1)) - 1;
        } else {
            lo = 0;
            hi = static_cast<int32_t>((1u << width) - 1u);
        }
        return true;
    }
    std::vector<CoverBinSpec> makeAutoBins(
        FileLine* fl, AstNodeExpr* exprp = nullptr,
        const std::vector<CoverpointPendingOption>* optionsp = nullptr) const {
        std::vector<CoverBinSpec> bins;
        const auto& options = optionsp ? *optionsp : m_coverpoint.options;
        const int autoBinMax = std::max(1, optionConstInt(options, "auto_bin_max", 64));
        int32_t lo = 0;
        int32_t hi = 0;
        if (!coverExprDiscreteDomain(exprp ? exprp : m_coverpoint.exprp, autoBinMax, lo, hi)) {
            return bins;
        }
        const int64_t count = static_cast<int64_t>(hi) - static_cast<int64_t>(lo) + 1;
        if (count <= 0) return bins;
        const int binCount = static_cast<int>(std::min<int64_t>(autoBinMax, count));
        const int64_t span = count / binCount;
        const int64_t rem = count % binCount;
        int64_t cur = lo;
        for (int i = 0; i < binCount; ++i) {
            const int64_t width = span + (i < rem ? 1 : 0);
            const int64_t next = cur + width - 1;
            bins.emplace_back(CoverBinSpec{fl,
                                           "__auto" + cvtToStr(i),
                                           newRangeExpr(fl, static_cast<int32_t>(cur),
                                                        static_cast<int32_t>(next)),
                                           nullptr,
                                           nullptr,
                                           nullptr,
                                           nullptr,
                                           nullptr,
                                           CoverBinKind::NORMAL,
                                           CoverTransRepeatKind::NONE,
                                           0,
                                           0,
                                           false,
                                           false,
                                           false,
                                           false,
                                           nullptr});
            cur = next + 1;
        }
        return bins;
    }
    std::vector<CoverBinSpec> makeAutoBinsForDType(
        FileLine* fl, const AstNodeDType* dtypep,
        const std::vector<CoverpointPendingOption>* optionsp = nullptr) const {
        std::vector<CoverBinSpec> bins;
        const auto& options = optionsp ? *optionsp : m_coverpoint.options;
        const int autoBinMax = std::max(1, optionConstInt(options, "auto_bin_max", 64));
        const AstNodeDType* const skipDtp = dtypep ? dtypep->skipRefp() : nullptr;
        const int width = skipDtp ? skipDtp->width() : 32;
        const bool isSigned = skipDtp ? skipDtp->isSigned() : true;
        int32_t lo = 0;
        int32_t hi = 0;
        if (width <= 0) return bins;
        if (!isSigned && width <= 30 && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
            lo = 0;
            hi = (1u << width) - 1;
        } else if (isSigned && width > 0 && width <= 16
                   && (1u << width) <= static_cast<unsigned>(autoBinMax)) {
            lo = -(1 << (width - 1));
            hi = (1 << (width - 1)) - 1;
        } else if (width == 1) {
            lo = isSigned ? -1 : 0;
            hi = 1;
        } else if (width > 31) {
            lo = std::numeric_limits<int32_t>::min();
            hi = std::numeric_limits<int32_t>::max();
        } else {
            if (isSigned) {
                lo = -(1 << (width - 1));
                hi = (1 << (width - 1)) - 1;
            } else {
                lo = 0;
                hi = static_cast<int32_t>((1u << width) - 1u);
            }
        }
        const int64_t count = static_cast<int64_t>(hi) - static_cast<int64_t>(lo) + 1;
        if (count <= 0) return bins;
        const int binCount = static_cast<int>(std::min<int64_t>(autoBinMax, count));
        const int64_t span = count / binCount;
        const int64_t rem = count % binCount;
        int64_t cur = lo;
        for (int i = 0; i < binCount; ++i) {
            const int64_t width64 = span + (i < rem ? 1 : 0);
            const int64_t next = cur + width64 - 1;
            bins.emplace_back(CoverBinSpec{
                fl, "__auto" + cvtToStr(i),
                newRangeExprForDType(fl, dtypep, static_cast<int32_t>(cur),
                                     static_cast<int32_t>(next)),
                nullptr, nullptr, nullptr, nullptr, nullptr, CoverBinKind::NORMAL,
                CoverTransRepeatKind::NONE, 0, 0, false, false, false, false, nullptr});
            cur = next + 1;
        }
        return bins;
    }
    std::vector<CoverBinSpec> expandArrayBins(const CoverBinSpec& bin) const {
        std::vector<CoverBinSpec> bins;
        std::vector<std::pair<int32_t, int32_t>> intervals;
        if (!bin.valueItemsp || !collectConstIntervals(bin.valueItemsp, intervals)) return bins;
        int64_t count = 0;
        for (const auto& interval : intervals) {
            count += static_cast<int64_t>(interval.second) - static_cast<int64_t>(interval.first) + 1;
        }
        if (count <= 0) return bins;
        int requested = 0;
        if (bin.unsizedArray) {
            if (bin.withp) {
                const int autoBinMax = std::max(1, optionConstInt(m_coverpoint.options, "auto_bin_max", 64));
                requested = static_cast<int>(std::min<int64_t>(count, autoBinMax));
            } else {
                requested = static_cast<int>(count);
            }
        } else {
            int32_t value = 0;
            if (!bin.arraySizep || !constExprToSInt(bin.arraySizep, value) || value <= 0) return bins;
            requested = value;
        }
        requested = static_cast<int>(std::max<int64_t>(1, std::min<int64_t>(requested, count)));
        const int64_t span = count / requested;
        const int64_t rem = count % requested;
        size_t intervalIdx = 0;
        int32_t curLo = intervals[0].first;
        int32_t curHi = intervals[0].second;
        for (int i = 0; i < requested; ++i) {
            int64_t remaining = span + (i < rem ? 1 : 0);
            std::vector<std::pair<int32_t, int32_t>> chunk;
            while (remaining > 0) {
                const int64_t avail
                    = static_cast<int64_t>(curHi) - static_cast<int64_t>(curLo) + 1;
                const int64_t take = std::min<int64_t>(remaining, avail);
                const int32_t takeHi = static_cast<int32_t>(curLo + take - 1);
                chunk.emplace_back(curLo, takeHi);
                remaining -= take;
                if (takeHi == curHi) {
                    ++intervalIdx;
                    if (remaining > 0 && intervalIdx >= intervals.size()) return {};
                    if (intervalIdx < intervals.size()) {
                        curLo = intervals[intervalIdx].first;
                        curHi = intervals[intervalIdx].second;
                    }
                } else {
                    curLo = takeHi + 1;
                }
            }
            bins.emplace_back(CoverBinSpec{
                bin.flp, bin.name + "[" + cvtToStr(i) + "]",
                newValueItemListFromIntervals(bin.flp, chunk), nullptr, nullptr,
                bin.withp ? bin.withp->cloneTreePure(false) : nullptr,
                bin.iffp ? bin.iffp->cloneTreePure(false) : nullptr, nullptr, bin.kind,
                CoverTransRepeatKind::NONE, 0, 0, bin.wildcard, false, false, false, nullptr});
        }
        return bins;
    }
    bool expandCoverpointBins() {
        if (!m_coverpoint.bins.empty()) {
            std::vector<CoverBinSpec> expanded;
            expanded.reserve(m_coverpoint.bins.size());
            for (CoverBinSpec& bin : m_coverpoint.bins) {
                if (bin.unsizedArray || bin.arraySizep) {
                    std::vector<CoverBinSpec> part = expandArrayBins(bin);
                    if (part.empty()) {
                        bin.flp->v3warn(V3ErrorCode::COVERIGN,
                                        "Ignoring unsupported: cover bin array specification");
                        return false;
                    }
                    expanded.insert(expanded.end(), std::make_move_iterator(part.begin()),
                                    std::make_move_iterator(part.end()));
                    deleteCoverBinSpec(bin);
                } else {
                    expanded.emplace_back(bin);
                    bin.valueItemsp = nullptr;
                    bin.transItemsp = nullptr;
                    bin.withp = nullptr;
                    bin.iffp = nullptr;
                    bin.arraySizep = nullptr;
                }
            }
            m_coverpoint.bins = std::move(expanded);
        }
        if (!m_coverpoint.bins.empty()) return true;
        const std::vector<CoverBinSpec> autoBins = makeAutoBins(m_coverpoint.flp);
        if (autoBins.empty()) return false;
        m_coverpoint.bins = autoBins;
        return true;
    }
    bool coverpointDetectOverlapEnabled() const {
        const int localValue = optionConstInt(m_coverpoint.options, "detect_overlap", -1);
        if (localValue >= 0) return localValue != 0;
        return optionConstInt(m_covergroup.options, "detect_overlap", 0) != 0;
    }
    static bool coverBinSupportsOverlapCheck(const CoverBinSpec& bin) {
        return bin.kind != CoverBinKind::DEFAULT && !bin.transition && !bin.wildcard && !bin.withp
               && bin.valueItemsp;
    }
    void warnCoverpointOverlap(const CoverBinSpec& lhs, const CoverBinSpec& rhs) const {
        lhs.flp->v3warn(V3ErrorCode::CASEOVERLAP,
                        "Coverage bins overlap: '" + lhs.name + "' and '" + rhs.name + "'\n"
                            + rhs.flp->warnOther()
                            + "... Location of overlapping coverage bin '" + rhs.name + "'\n"
                            + rhs.flp->warnContextSecondary());
    }
    void detectCoverpointOverlaps() const {
        if (!coverpointDetectOverlapEnabled()) return;
        for (size_t i = 0; i < m_coverpoint.bins.size(); ++i) {
            const CoverBinSpec& lhs = m_coverpoint.bins[i];
            if (!coverBinSupportsOverlapCheck(lhs)) continue;
            for (size_t j = i + 1; j < m_coverpoint.bins.size(); ++j) {
                const CoverBinSpec& rhs = m_coverpoint.bins[j];
                if (!coverBinSupportsOverlapCheck(rhs)) continue;
                if (!rangeListOverlaps(lhs.valueItemsp, rhs.valueItemsp)) continue;
                warnCoverpointOverlap(lhs, rhs);
            }
        }
    }
    AstNodeExpr* materializeCoverBinWithCond(const CoverBinSpec& bin) const {
        return instantiateCoverWithCond(bin.withp, m_coverpoint.exprp->cloneTreePure(false));
    }
    AstNodeExpr* makeCoverValueMatchCond(FileLine* fl, AstNodeExpr* sampleExprp, AstNodeExpr* valueItemsp,
                                         bool wildcard) const {
        if (!valueItemsp) return nullptr;
        if (wildcard) {
            AstNodeExpr* condp = nullptr;
            for (AstNodeExpr* itemp = valueItemsp; itemp; itemp = VN_AS(itemp->nextp(), NodeExpr)) {
                AstNodeExpr* const matchp
                    = new AstEqWild{fl, sampleExprp->cloneTreePure(false), itemp->cloneTreePure(false)};
                matchp->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
                condp = condp ? makeCoverLogOr(fl, condp, matchp) : matchp;
            }
            return condp;
        }
        AstInside* const insidep
            = new AstInside{fl, sampleExprp->cloneTreePure(false), valueItemsp->cloneTreePure(true)};
        insidep->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
        return insidep;
    }
    AstNodeExpr* makeCoverIntInRangeCond(FileLine* fl, AstNodeExpr* exprp, int lo, int hi) const {
        AstNodeExpr* condp = nullptr;
        if (lo > std::numeric_limits<int32_t>::min()) {
            condp = new AstGte{fl, exprp->cloneTreePure(false), newIntConst(fl, lo)};
        }
        if (hi < std::numeric_limits<int32_t>::max()) {
            AstNodeExpr* const hip = new AstLte{fl, exprp->cloneTreePure(false), newIntConst(fl, hi)};
            condp = condp ? makeCoverLogAnd(fl, condp, hip) : hip;
        }
        if (!condp) condp = new AstConst{fl, AstConst::BitTrue{}};
        return condp;
    }
    AstNodeExpr* makeCoverBinSampleEnableCond(const CoverBinSpec& bin) const {
        AstNodeExpr* condp = nullptr;
        if (m_coverpoint.iffp) {
            condp = suppressGeneratedCoverageCondWarns(m_coverpoint.iffp->cloneTreePure(false));
        }
        if (bin.iffp) {
            AstNodeExpr* const binCondp
                = suppressGeneratedCoverageCondWarns(bin.iffp->cloneTreePure(false));
            condp = condp ? makeCoverLogAnd(bin.flp, condp, binCondp) : binCondp;
        }
        return condp;
    }
    AstNodeExpr* makeCoverBinCond(const CoverBinSpec& bin) const {
        if (bin.kind == CoverBinKind::DEFAULT) return nullptr;
        AstNodeExpr* condp = nullptr;
        if (bin.transRepeatKind != CoverTransRepeatKind::NONE) {
            if (!bin.transCountVarp || !bin.transRepeatValueItemsp) return nullptr;
            AstNodeExpr* const matchp = makeCoverValueMatchCond(
                bin.flp, m_coverpoint.exprp, bin.transRepeatValueItemsp, bin.wildcard);
            if (!matchp) return nullptr;
            AstNodeExpr* const nextCountp
                = new AstAdd{bin.flp,
                             new AstVarRef{bin.flp, bin.transCountVarp, VAccess::READ},
                             newIntConst(bin.flp, 1)};
            condp = makeCoverLogAnd(
                bin.flp, matchp,
                makeCoverIntInRangeCond(bin.flp, nextCountp, bin.transRepeatMin, bin.transRepeatMax));
        } else if (bin.transition) {
            std::vector<AstArg*> steps;
            for (AstNode* nodep = bin.transItemsp; nodep; nodep = nodep->nextp()) {
                AstArg* const argp = VN_CAST(nodep, Arg);
                if (!argp || !argp->exprp()) return nullptr;
                steps.push_back(argp);
            }
            if (steps.size() != 2) return nullptr;
            if (!m_coverpoint.prevVarp || !m_coverpoint.prevValidVarp) return nullptr;
            AstNodeExpr* const prevValidp
                = new AstVarRef{bin.flp, m_coverpoint.prevValidVarp, VAccess::READ};
            AstNodeExpr* const prevRefp
                = new AstVarRef{bin.flp, m_coverpoint.prevVarp, VAccess::READ};
            AstNodeExpr* const prevCondp = makeCoverValueMatchCond(
                bin.flp, prevRefp, steps[0]->exprp(), bin.wildcard);
            AstNodeExpr* const curCondp = makeCoverValueMatchCond(
                bin.flp, m_coverpoint.exprp, steps[1]->exprp(), bin.wildcard);
            if (!prevCondp || !curCondp) return nullptr;
            condp = makeCoverLogAnd(bin.flp, prevValidp,
                                    makeCoverLogAnd(bin.flp, prevCondp, curCondp));
        } else if (bin.valueItemsp) {
            condp = makeCoverValueMatchCond(bin.flp, m_coverpoint.exprp, bin.valueItemsp, bin.wildcard);
        }
        if (AstNodeExpr* const withCondp = materializeCoverBinWithCond(bin)) {
            if (bin.transition) {
                VL_DO_DANGLING(withCondp->deleteTree(), withCondp);
                return nullptr;
            }
            condp = condp ? makeCoverLogAnd(bin.flp, condp, withCondp) : withCondp;
        }
        if (AstNodeExpr* const enablep = makeCoverBinSampleEnableCond(bin)) {
            condp = condp ? makeCoverLogAnd(bin.flp, enablep, condp) : enablep;
        }
        return condp;
    }
    static const char* coverTransRepeatMarker(CoverTransRepeatKind kind) {
        switch (kind) {
        case CoverTransRepeatKind::CONSEC: return "[*]";
        case CoverTransRepeatKind::GOTO: return "[->]";
        case CoverTransRepeatKind::NONCONSEC: return "[=]";
        default: return "";
        }
    }
    static CoverTransRepeatKind coverTransRepeatKindFromMarker(const string& name) {
        if (name == "[*]") return CoverTransRepeatKind::CONSEC;
        if (name == "[->]") return CoverTransRepeatKind::GOTO;
        if (name == "[=]") return CoverTransRepeatKind::NONCONSEC;
        return CoverTransRepeatKind::NONE;
    }
    AstNode* makeCoverTransStep(AstNode* itemsp) const {
        if (!itemsp) return nullptr;
        if (VN_IS(itemsp, Arg)) return itemsp;
        return new AstArg{itemsp->fileline(), "", VN_AS(itemsp, NodeExpr)};
    }
    AstNode* makeCoverTransRepeatStep(FileLine* fl, AstNode* itemsp, CoverTransRepeatKind kind,
                                      AstNodeExpr* minp, AstNodeExpr* maxp) const {
        if (!itemsp || kind == CoverTransRepeatKind::NONE || !minp) {
            if (itemsp) itemsp->deleteTree();
            if (minp) minp->deleteTree();
            if (maxp) maxp->deleteTree();
            return nullptr;
        }
        AstArg* const markerp
            = new AstArg{fl, coverTransRepeatMarker(kind), VN_AS(itemsp, NodeExpr)};
        markerp->addNext(new AstArg{fl, "min", minp});
        if (maxp) markerp->addNext(new AstArg{fl, "max", maxp});
        return markerp;
    }
    struct ParsedCoverTransStep final {
        AstNodeExpr* valueItemsp = nullptr;
        CoverTransRepeatKind repeatKind = CoverTransRepeatKind::NONE;
        int repeatMin = 0;
        int repeatMax = 0;
    };
    static void deleteParsedCoverTransSteps(std::vector<ParsedCoverTransStep>& steps) {
        for (ParsedCoverTransStep& step : steps) {
            if (step.valueItemsp) VL_DO_DANGLING(step.valueItemsp->deleteTree(), step.valueItemsp);
        }
        steps.clear();
    }
    bool parseCoverTransitionSteps(FileLine* fl, AstNode* transItemsp,
                                   std::vector<ParsedCoverTransStep>& steps) const {
        for (AstNode* nodep = transItemsp; nodep;) {
            AstArg* const argp = VN_CAST(nodep, Arg);
            if (!argp || !argp->exprp()) return false;
            ParsedCoverTransStep step;
            step.valueItemsp = static_cast<AstNodeExpr*>(argp->exprp()->cloneTree(true));
            step.repeatKind = coverTransRepeatKindFromMarker(argp->name());
            nodep = argp->nextp();
            if (step.repeatKind == CoverTransRepeatKind::NONE) {
                steps.push_back(step);
                continue;
            }
            AstArg* const minArgp = VN_CAST(nodep, Arg);
            if (!minArgp || minArgp->name() != "min" || !minArgp->exprp()) return false;
            int32_t minValue = 0;
            if (!constExprToSInt(minArgp->exprp(), minValue) || minValue <= 0) return false;
            nodep = minArgp->nextp();
            int32_t maxValue = minValue;
            if (AstArg* const maxArgp = VN_CAST(nodep, Arg)) {
                if (maxArgp->name() == "max") {
                    if (!maxArgp->exprp() || !constExprToSInt(maxArgp->exprp(), maxValue)
                        || maxValue < minValue) {
                        return false;
                    }
                    nodep = maxArgp->nextp();
                }
            }
            step.repeatMin = minValue;
            step.repeatMax = maxValue;
            steps.push_back(step);
        }
        return !steps.empty();
    }
    AstNode* makeCoverBinAction(const CoverBinSpec& bin, AstVar* instVarp, AstVar* typeVarp,
                                AstCoverOtherDecl* declp, int binNum) const {
        AstNode* bodysp = nullptr;
        if (declp) {
            const char* const hitMethod = (bin.kind == CoverBinKind::DEFAULT)
                                              ? "verilator_cov_hit_once"
                                              : "verilator_cov_hit";
            AstMethodCall* const instHitp
                = new AstMethodCall{bin.flp, new AstVarRef{bin.flp, instVarp, VAccess::READWRITE},
                                    hitMethod,
                                    new AstArg{bin.flp, "", newIntConst(bin.flp, binNum)}};
            instHitp->dtypeSetVoid();
            AstMethodCall* const typeHitp
                = new AstMethodCall{bin.flp, new AstVarRef{bin.flp, typeVarp, VAccess::READWRITE},
                                    hitMethod,
                                    new AstArg{bin.flp, "", newIntConst(bin.flp, binNum)}};
            typeHitp->dtypeSetVoid();
            bodysp = instHitp->makeStmt();
            AstNode::addNext(bodysp, typeHitp->makeStmt());
            AstNode::addNext(bodysp, new AstCoverInc{bin.flp, declp});
        }
        if (bin.kind == CoverBinKind::ILLEGAL) {
            AstDisplay* const errp = new AstDisplay{
                bin.flp, VDisplayType::DT_ERROR,
                "Illegal cover bin hit: " + m_coverpoint.name + "." + bin.name, nullptr, nullptr};
            bodysp = AstNode::addNextNull(bodysp, errp);
        }
        return bodysp;
    }
    const CoverpointInfo* findCoverpointInfo(const string& name) const {
        for (const CoverpointInfo& info : m_covergroup.coverpoints) {
            if (info.name == name) return &info;
        }
        for (const CoverpointInfo& info : m_covercross.implicitInfos) {
            if (info.name == name) return &info;
        }
        return nullptr;
    }
    const CoverpointBinInfo* findCoverpointBinInfo(const CoverpointInfo& info,
                                                   const string& name) const {
        for (const CoverpointBinInfo& bin : info.bins) {
            if (bin.name == name) return &bin;
        }
        return nullptr;
    }
    AstNodeExpr* makeCoverpointBinSelectCond(FileLine* fl, const CoverpointInfo& info,
                                             const std::vector<std::string>& binNames = {},
                                             bool selectNone = false) const {
        if (selectNone) return new AstConst{fl, AstConst::BitFalse{}};
        AstNodeExpr* condp = nullptr;
        if (binNames.empty()) {
            for (const CoverpointBinInfo& bin : info.bins) {
                AstNodeExpr* const itemp = bin.condp->cloneTreePure(false);
                condp = condp ? static_cast<AstNodeExpr*>(new AstLogOr{fl, condp, itemp}) : itemp;
            }
            return condp;
        }
        for (const std::string& binName : binNames) {
            const CoverpointBinInfo* const binp = findCoverpointBinInfo(info, binName);
            if (!binp) return nullptr;
            AstNodeExpr* const itemp = binp->condp->cloneTreePure(false);
            condp = condp ? static_cast<AstNodeExpr*>(new AstLogOr{fl, condp, itemp}) : itemp;
        }
        return condp;
    }
    const CoverCrossSelection* findCoverCrossSelection(const CoverCrossClause& clause,
                                                       const string& coverpointName) const {
        for (const CoverCrossSelection& sel : clause.selections) {
            if (sel.coverpointName == coverpointName) return &sel;
        }
        return nullptr;
    }
    bool resolveCoverCrossSelectionBins(const CoverCrossSelection& selection,
                                        const CoverpointInfo& info,
                                        std::vector<std::string>& out) const {
        std::vector<std::string> allBins;
        allBins.reserve(info.bins.size());
        for (const CoverpointBinInfo& bin : info.bins) allBins.push_back(bin.name);
        if (selection.selectNone) {
            out.clear();
            return true;
        }
        std::vector<std::string> chosen;
        if (selection.binNames.empty()) {
            chosen = allBins;
        } else {
            for (const std::string& wanted : selection.binNames) {
                if (std::find(allBins.begin(), allBins.end(), wanted) == allBins.end()) return false;
            }
            for (const std::string& binName : allBins) {
                if (std::find(selection.binNames.begin(), selection.binNames.end(), binName)
                    != selection.binNames.end()) {
                    chosen.push_back(binName);
                }
            }
        }
        if (selection.invert) {
            for (const std::string& binName : allBins) {
                if (std::find(chosen.begin(), chosen.end(), binName) == chosen.end()) {
                    out.push_back(binName);
                }
            }
        } else {
            out = std::move(chosen);
        }
        return true;
    }
    bool mergeCoverCrossSelection(CoverCrossSelection& dst, const CoverCrossSelection& src) const {
        if (dst.coverpointName != src.coverpointName) return false;
        const CoverpointInfo* const infop = findCoverpointInfo(dst.coverpointName);
        if (!infop) return false;
        std::vector<std::string> dstBins;
        std::vector<std::string> srcBins;
        if (!resolveCoverCrossSelectionBins(dst, *infop, dstBins)
            || !resolveCoverCrossSelectionBins(src, *infop, srcBins)) {
            return false;
        }
        std::vector<std::string> merged;
        for (const CoverpointBinInfo& bin : infop->bins) {
            const bool inDst = std::find(dstBins.begin(), dstBins.end(), bin.name) != dstBins.end();
            const bool inSrc = std::find(srcBins.begin(), srcBins.end(), bin.name) != srcBins.end();
            if (inDst && inSrc) merged.push_back(bin.name);
        }
        dst.invert = false;
        dst.selectNone = merged.empty();
        if (!dst.selectNone && merged.size() == infop->bins.size()) {
            dst.binNames.clear();
        } else {
            dst.binNames = std::move(merged);
        }
        return true;
    }
    static AstNode* makeCoverCrossSelectOrMarker(FileLine* fl) {
        return new AstArg{fl, "||", nullptr};
    }
    static bool isCoverCrossSelectOrMarker(AstNode* nodep) {
        if (AstArg* const argp = VN_CAST(nodep, Arg)) return argp->name() == "||" && !argp->exprp();
        return false;
    }
    static AstNode* appendCoverCrossSelectNode(AstNode* headp, AstNode*& tailp, AstNode* nodep) {
        if (!nodep) return headp;
        if (tailp) {
            tailp->addNext(nodep);
        } else {
            headp = nodep;
        }
        for (tailp = nodep; tailp->nextp(); tailp = tailp->nextp()) {}
        return headp;
    }
    AstNode* appendCoverCrossWith(AstNode* selectionsp, FileLine* fl, AstNodeExpr* withp) {
        if (!selectionsp) {
            if (withp) VL_DO_DANGLING(withp->deleteTree(), withp);
            return nullptr;
        }
        bool sawOr = false;
        for (AstNode* nodep = selectionsp; nodep; nodep = nodep->nextp()) {
            if (isCoverCrossSelectOrMarker(nodep)) {
                sawOr = true;
                break;
            }
        }
        if (!sawOr) return AstNode::addNextNull<AstNode, AstNode>(selectionsp,
                                                                  new AstArg{fl, "", withp});
        AstNode* newSelectionsp = nullptr;
        AstNode* tailp = nullptr;
        for (AstNode* nodep = selectionsp; nodep; nodep = nodep->nextp()) {
            if (isCoverCrossSelectOrMarker(nodep)) {
                newSelectionsp = appendCoverCrossSelectNode(
                    newSelectionsp, tailp, new AstArg{fl, "", withp->cloneTreePure(false)});
            }
            newSelectionsp
                = appendCoverCrossSelectNode(newSelectionsp, tailp, nodep->cloneTreePure(false));
        }
        newSelectionsp
            = appendCoverCrossSelectNode(newSelectionsp, tailp, new AstArg{fl, "", withp});
        VL_DO_DANGLING(selectionsp->deleteTree(), selectionsp);
        return newSelectionsp;
    }
    static std::string crossItemName(AstNode* nodep) {
        if (!nodep) return "";
        if (AstParseRef* const refp = VN_CAST(nodep, ParseRef)) return refp->name();
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp->name();
        if (AstMemberSel* const selp = VN_CAST(nodep, MemberSel)) {
            const std::string fromName = crossItemName(selp->fromp());
            return fromName.empty() ? selp->name() : fromName + "." + selp->name();
        }
        if (AstDot* const dotp = VN_CAST(nodep, Dot)) {
            const std::string lhsName = crossItemName(dotp->lhsp());
            const std::string rhsName = crossItemName(dotp->rhsp());
            if (lhsName.empty() || rhsName.empty()) return "";
            return lhsName + (dotp->colon() ? "::" : ".") + rhsName;
        }
        return "";
    }
    static std::pair<std::string, std::string> splitCoverCrossItemName(const std::string& fullName) {
        const size_t dotPos = fullName.rfind('.');
        if (dotPos == std::string::npos) return {fullName, ""};
        return {fullName.substr(0, dotPos), fullName.substr(dotPos + 1)};
    }
    AstNodeExpr* makeCoverPlusMinusRange(FileLine* fl, AstNodeExpr* centerp, AstNodeExpr* deltap) const {
        if (!centerp || !deltap) {
            if (centerp) centerp->deleteTree();
            if (deltap) deltap->deleteTree();
            return nullptr;
        }
        AstNodeExpr* const loExprp
            = new AstSub{fl, centerp->cloneTreePure(false), deltap->cloneTreePure(false)};
        AstNodeExpr* const hiExprp = new AstAdd{fl, centerp, deltap};
        loExprp->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
        hiExprp->fileline()->warnOff(V3ErrorCode::WIDTHEXPAND, true);
        return new AstInsideRange{fl, loExprp, hiExprp};
    }
    AstNodeExpr* makeCoverExprReal(FileLine* fl, AstNodeExpr* exprp) const {
        if (!exprp) return nullptr;
        if (exprp->isDouble()) return exprp;
        AstNodeDType* const dtypep = inferCoverExprDType(fl, exprp);
        const AstNodeDType* const skipDtp = dtypep ? dtypep->skipRefp() : nullptr;
        const bool isSigned = skipDtp ? skipDtp->isSigned() : true;
        if (dtypep && !dtypep->generic()) VL_DO_DANGLING(dtypep->deleteTree(), dtypep);
        return isSigned ? static_cast<AstNodeExpr*>(new AstISToRD{fl, exprp})
                        : static_cast<AstNodeExpr*>(new AstIToRD{fl, exprp});
    }
    AstNodeExpr* makeCoverPctPlusMinusRange(FileLine* fl, AstNodeExpr* centerp,
                                            AstNodeExpr* pctp) const {
        if (!centerp || !pctp) {
            if (centerp) centerp->deleteTree();
            if (pctp) pctp->deleteTree();
            return nullptr;
        }
        AstNodeExpr* const deltaRealp = new AstDivD{
            fl,
            new AstMulD{fl, makeCoverExprReal(fl, centerp->cloneTreePure(false)),
                        makeCoverExprReal(fl, pctp)},
            new AstConst{fl, AstConst::RealDouble{}, 100.0}};
        AstNodeExpr* const deltap = new AstRToIS{fl, deltaRealp};
        return makeCoverPlusMinusRange(fl, centerp, deltap);
    }
    AstNodeExpr* instantiateCoverWithCond(AstNodeExpr* withp, AstNodeExpr* itemExprp) const {
        if (!withp) {
            if (itemExprp) itemExprp->deleteTree();
            return nullptr;
        }
        AstNodeExpr* const condp = withp->cloneTreePure(false);
        std::vector<AstParseRef*> itemRefs;
        std::vector<AstVarRef*> itemVarRefs;
        condp->foreach([&](AstParseRef* refp) {
            if (refp->name() == "item" && !refp->lhsp()) itemRefs.push_back(refp);
        });
        condp->foreach([&](AstVarRef* refp) {
            if (refp->name() == "item") itemVarRefs.push_back(refp);
        });
        for (AstParseRef* const refp : itemRefs) {
            refp->replaceWith(itemExprp->cloneTreePure(false));
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        for (AstVarRef* const refp : itemVarRefs) {
            refp->replaceWith(itemExprp->cloneTreePure(false));
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
        if (itemExprp) itemExprp->deleteTree();
        return condp;
    }
    AstNodeExpr* makeCoverExprDomainValueItems(FileLine* fl,
                                             AstNodeExpr* domainExprp = nullptr) const {
        int32_t lo = 0;
        int32_t hi = 0;
        AstNodeExpr* const exprp = domainExprp ? domainExprp : m_coverpoint.exprp;
        if (!coverExprDiscreteDomain(exprp, std::numeric_limits<int>::max(), lo, hi)) return nullptr;
        return newValueItemListFromIntervals(fl, {{lo, hi}});
    }
    AstNodeExpr* makeFilteredCoverExprValueItems(FileLine* fl, AstNodeExpr* withp,
                                                 AstNodeExpr* domainExprp = nullptr) const {
        int32_t lo = 0;
        int32_t hi = 0;
        AstNodeExpr* const exprp = domainExprp ? domainExprp : m_coverpoint.exprp;
        if (!coverExprDiscreteDomain(exprp, 1024, lo, hi)) return nullptr;
        const int64_t count = static_cast<int64_t>(hi) - static_cast<int64_t>(lo) + 1;
        if (count <= 0 || count > 1024) return nullptr;
        std::vector<std::pair<int32_t, int32_t>> intervals;
        bool inRange = false;
        int32_t rangeLo = 0;
        for (int64_t value = lo; value <= hi; ++value) {
            AstNodeExpr* const condp
                = instantiateCoverWithCond(withp, newCoverExprConst(fl, static_cast<int32_t>(value)));
            int32_t condValue = 0;
            if (!condp || !constExprToSInt(condp, condValue)) {
                if (condp) VL_DO_DANGLING(condp->deleteTree(), condp);
                return nullptr;
            }
            VL_DO_DANGLING(condp->deleteTree(), condp);
            if (condValue) {
                if (!inRange) {
                    rangeLo = static_cast<int32_t>(value);
                    inRange = true;
                }
            } else if (inRange) {
                intervals.emplace_back(rangeLo, static_cast<int32_t>(value - 1));
                inRange = false;
            }
        }
        if (inRange) intervals.emplace_back(rangeLo, hi);
        if (intervals.empty()) return new AstConst{fl, AstConst::BitFalse{}};
        return newValueItemListFromIntervals(fl, intervals);
    }
    bool rangeListOverlaps(AstNodeExpr* valueItemsp, AstNode* filterItemsp) const {
        for (AstNodeExpr* valuep = valueItemsp; valuep; valuep = VN_AS(valuep->nextp(), NodeExpr)) {
            int32_t valueLo = 0;
            int32_t valueHi = 0;
            if (!constRangeEndpoints(valuep, valueLo, valueHi)) return false;
            for (AstNode* filterp = filterItemsp; filterp; filterp = filterp->nextp()) {
                AstNodeExpr* const filterExprp = VN_CAST(filterp, NodeExpr);
                int32_t filterLo = 0;
                int32_t filterHi = 0;
                if (!filterExprp || !constRangeEndpoints(filterExprp, filterLo, filterHi)) return false;
                if (valueLo <= filterHi && filterLo <= valueHi) return true;
            }
        }
        return false;
    }
    const CoverpointInfo* makeImplicitCrossCoverpointInfo(FileLine* fl, const string& name,
                                                          AstNodeExpr* exprp) {
        if (!exprp) return nullptr;
        if (m_covergroup.extendsUnsupported && m_covergroup.ownerInClass) {
            VL_DO_DANGLING(exprp->deleteTree(), exprp);
            return nullptr;
        }
        AstVar* const varp = [&]() -> AstVar* {
            if (AstVar* const resolvedp = resolveDirectCoverVar(exprp)) return resolvedp;
            return findDeclaredCoverVarByName(name);
        }();
        if (varp) {
            VL_DO_DANGLING(exprp->deleteTree(), exprp);
            exprp = new AstVarRef{fl, varp, VAccess::READ};
        }
        AstNodeExpr* sampleExprp = exprp;
        if (m_covergroup.eventDriven) sampleExprp = addHiddenCoverSampleArg(fl, "cg_crossitem_", exprp);
        const AstNodeDType* crossVarDTypep = nullptr;
        if (varp) {
            crossVarDTypep = varp->subDTypep();
            if (!crossVarDTypep || !crossVarDTypep->skipRefp() || crossVarDTypep->skipRefp()->width() <= 0) {
                crossVarDTypep = varp->dtypep();
            }
        }
        std::vector<CoverBinSpec> binSpecs
            = crossVarDTypep ? makeAutoBinsForDType(fl, crossVarDTypep) : makeAutoBins(fl, sampleExprp);
        if (binSpecs.empty()) {
            VL_DO_DANGLING(sampleExprp->deleteTree(), sampleExprp);
            return nullptr;
        }
        CoverpointInfo info;
        info.name = name;
        info.totalBins = static_cast<int>(binSpecs.size());
        for (CoverBinSpec& bin : binSpecs) {
            AstNodeExpr* const condp
                = makeCoverValueMatchCond(bin.flp, sampleExprp, bin.valueItemsp, bin.wildcard);
            if (!condp) {
                deleteCoverBinSpec(bin);
                deleteCoverpointInfoBins(info);
                VL_DO_DANGLING(sampleExprp->deleteTree(), sampleExprp);
                return nullptr;
            }
            info.bins.emplace_back(CoverpointBinInfo{
                bin.name, 0, condp,
                bin.valueItemsp ? static_cast<AstNodeExpr*>(bin.valueItemsp->cloneTree(true))
                                : nullptr});
            deleteCoverBinSpec(bin);
        }
        VL_DO_DANGLING(sampleExprp->deleteTree(), sampleExprp);
        m_covercross.implicitInfos.emplace_back(std::move(info));
        return &m_covercross.implicitInfos.back();
    }
    AstNode* makeCoverCrossSelectExpr(AstNodeExpr* binsExprp, AstNode* filterItemsp = nullptr,
                                      bool invert = false) {
        if (!binsExprp) {
            if (filterItemsp) filterItemsp->deleteTree();
            return nullptr;
        }
        FileLine* const fl = binsExprp->fileline();
        const std::string fullName = crossItemName(binsExprp);
        auto splitName = splitCoverCrossItemName(fullName);
        if (splitName.first.empty()) {
            VL_DO_DANGLING(binsExprp->deleteTree(), binsExprp);
            if (filterItemsp) filterItemsp->deleteTree();
            return nullptr;
        }
        AstNodeExpr* binNameListp = nullptr;
        bool selectNone = false;
        if (filterItemsp) {
            const CoverpointInfo* const infop = findCoverpointInfo(splitName.first);
            if (!infop) {
                VL_DO_DANGLING(binsExprp->deleteTree(), binsExprp);
                filterItemsp->deleteTree();
                return nullptr;
            }
            for (const CoverpointBinInfo& bin : infop->bins) {
                if (!splitName.second.empty() && bin.name != splitName.second) continue;
                if (!bin.valueItemsp || !rangeListOverlaps(bin.valueItemsp, filterItemsp)) continue;
                AstNodeExpr* const namep = new AstParseRef{fl, bin.name};
                binNameListp = binNameListp
                                   ? AstNode::addNextNull<AstNodeExpr, AstNodeExpr>(binNameListp, namep)
                                   : namep;
            }
            if (!binNameListp) selectNone = true;
            filterItemsp->deleteTree();
        } else if (!splitName.second.empty()) {
            binNameListp = new AstParseRef{fl, splitName.second};
        }
        VL_DO_DANGLING(binsExprp->deleteTree(), binsExprp);
        if (selectNone) binNameListp = new AstConst{fl, AstConst::BitFalse{}};
        return new AstArg{fl, invert ? "!" + splitName.first : splitName.first, binNameListp};
    }
    std::string defaultCrossName(AstNode* itemsp) {
        std::string name = "verilator_cov_cross";
        bool first = true;
        for (AstNode* itemp = itemsp; itemp; itemp = itemp->nextp()) {
            const std::string itemName = crossItemName(itemp);
            if (itemName.empty()) continue;
            name += first ? "_" : "__";
            name += itemName;
            first = false;
        }
        if (first) name += cvtToStr(m_covergroup.autoCrossNum++);
        return name;
    }
    void cleanupCoverCrossState() {
        if (m_covercross.iffp) VL_DO_DANGLING(m_covercross.iffp->deleteTree(), m_covercross.iffp);
        for (CoverpointInfo& info : m_covercross.implicitInfos) deleteCoverpointInfoBins(info);
        for (CoverCrossBinSpec& bin : m_covercross.bins) deleteCoverCrossBinSpec(bin);
        for (CoverpointPendingOption& opt : m_covercross.options) {
            if (opt.valuep) VL_DO_DANGLING(opt.valuep->deleteTree(), opt.valuep);
        }
        m_covercross = CoverCrossState{};
    }
    static bool crossOptionMemberSupported(const string& member, bool typeOption) {
        if (typeOption) return member == "weight" || member == "goal" || member == "comment";
        return member == "weight" || member == "goal" || member == "comment"
               || member == "at_least" || member == "cross_num_print_missing";
    }
    static string coverCrossSelectFunctionPrefix() { return "\001covercross_func\001"; }
    static string coverCrossSelectFunctionMarker(const string& name) {
        return coverCrossSelectFunctionPrefix() + name;
    }
    static bool isCoverCrossSelectFunctionMarker(const string& name) {
        return name.rfind(coverCrossSelectFunctionPrefix(), 0) == 0;
    }
    static string coverCrossSelectFunctionName(const string& marker) {
        return isCoverCrossSelectFunctionMarker(marker)
                   ? marker.substr(coverCrossSelectFunctionPrefix().size())
                   : marker;
    }
    void coverCrossUnsupported(FileLine* fl, const string& msg) {
        if (fl) fl->v3warn(V3ErrorCode::COVERIGN, msg);
        m_covercross.unsupported = true;
    }
    void addCoverCrossBodyFunction(AstNode* declp) {
        if (declp) VL_DO_DANGLING(declp->deleteTree(), declp);
    }
    AstNode* makeCoverCrossSelectFunctionCall(FileLine* fl, const string& name, AstNode* argsp) {
        if (argsp) VL_DO_DANGLING(argsp->deleteTree(), argsp);
        return new AstArg{fl, coverCrossSelectFunctionMarker(name), nullptr};
    }
    void startCoverCross(FileLine* fl, const string& name, AstNode* itemsp, AstNodeExpr* iffp) {
        cleanupCoverCrossState();
        if (!m_covergroup.active) {
            if (itemsp) itemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return;
        }
        if (m_covergroup.extendsUnsupported) {
            if (fl) fl->v3warn(V3ErrorCode::COVERIGN, "Ignoring unsupported: covergroup extends");
            if (itemsp) itemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            m_covercross.unsupported = true;
            return;
        }
        size_t itemCount = 0;
        for (AstNode* itemp = itemsp; itemp; itemp = itemp->nextp()) ++itemCount;
        m_covercross.implicitInfos.reserve(itemCount);
        std::vector<const CoverpointInfo*> infos;
        for (AstNode* itemp = itemsp; itemp; itemp = itemp->nextp()) {
            const std::string itemName = crossItemName(itemp);
            const CoverpointInfo* infop = itemName.empty() ? nullptr : findCoverpointInfo(itemName);
            if (!infop) {
                AstNodeExpr* const exprp = itemp ? VN_CAST(itemp->cloneTreePure(false), NodeExpr) : nullptr;
                infop = itemName.empty() ? nullptr : makeImplicitCrossCoverpointInfo(fl, itemName, exprp);
            }
            if (!infop || infop->totalBins <= 0
                || infop->bins.size() != static_cast<size_t>(infop->totalBins)) {
                fl->v3warn(V3ErrorCode::COVERIGN,
                           "Ignoring unsupported: cover cross item '" + itemName
                               + "' requires a supported coverpoint or auto-binnable expression");
                if (itemsp) itemsp->deleteTree();
                if (iffp) iffp->deleteTree();
                return;
            }
            infos.push_back(infop);
        }
        if (infos.size() < 2) {
            fl->v3warn(V3ErrorCode::COVERIGN,
                       "Ignoring unsupported: cover cross requires at least two coverpoints");
            if (itemsp) itemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return;
        }
        if (m_covergroup.eventDriven && iffp) iffp = addHiddenCoverSampleArg(fl, "cg_crossiff_", iffp);
        m_covercross.active = true;
        m_covercross.flp = fl;
        m_covercross.name = name.empty() ? defaultCrossName(itemsp) : name;
        m_covercross.iffp = iffp;
        m_covercross.infos = std::move(infos);
        if (itemsp) itemsp->deleteTree();
    }
    AstNode* addCoverCrossBodyBin(FileLine* fl, const string& name, AstNode* selectionsp,
                                  AstNodeExpr* iffp,
                                  CoverBinKind kind = CoverBinKind::NORMAL) {
        if (!m_covercross.active) {
            if (selectionsp) selectionsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return nullptr;
        }
        if (!selectionsp) {
            coverCrossUnsupported(fl, "Ignoring unsupported: coverage cross bin");
            if (iffp) VL_DO_DANGLING(iffp->deleteTree(), iffp);
            return nullptr;
        }
        CoverCrossBinSpec spec;
        spec.flp = fl;
        spec.name = name;
        spec.iffp = iffp;
        spec.kind = kind;
        CoverCrossClause clause;
        bool sawClauseItem = false;
        const auto finishClause = [&]() -> bool {
            if (!sawClauseItem && !clause.iffp) return false;
            spec.clauses.push_back(std::move(clause));
            clause = CoverCrossClause{};
            sawClauseItem = false;
            return true;
        };
        for (AstNode* selp = selectionsp; selp; selp = selp->nextp()) {
            if (AstArg* const argp = VN_CAST(selp, Arg)) {
                if (isCoverCrossSelectFunctionMarker(argp->name())) {
                    fl->v3error("Coverage select function call '"
                                << coverCrossSelectFunctionName(argp->name())
                                << "' is not supported in cross bin selections");
                    if (selectionsp) selectionsp->deleteTree();
                    return nullptr;
                }
                if (argp->name() == "||" && !argp->exprp()) {
                    if (!finishClause()) {
                        coverCrossUnsupported(
                            fl, "Ignoring unsupported: malformed cover cross bin selection");
                        if (selectionsp) selectionsp->deleteTree();
                        return nullptr;
                    }
                    continue;
                }
            }
            CoverCrossSelection selection;
            if (AstArg* const argp = VN_CAST(selp, Arg)) {
                selection.coverpointName = argp->name();
                if (!selection.coverpointName.empty() && selection.coverpointName[0] == '!') {
                    selection.invert = true;
                    selection.coverpointName.erase(0, 1);
                }
                if (selection.coverpointName.empty()) {
                    if (AstNodeExpr* const exprp = argp->exprp()) {
                        AstNodeExpr* const withp = exprp->cloneTreePure(false);
                        clause.iffp = clause.iffp ? makeCoverLogAnd(fl, clause.iffp, withp) : withp;
                        sawClauseItem = true;
                    }
                    continue;
                }
                if (AstNodeExpr* exprp = argp->exprp()) {
                    if (VN_IS(exprp, Const) && VN_AS(exprp, Const)->isZero()) {
                        selection.selectNone = true;
                    } else {
                        for (AstNodeExpr* itemp = exprp; itemp; itemp = VN_AS(itemp->nextp(), NodeExpr)) {
                            const std::string binName = crossItemName(itemp);
                            if (binName.empty()) {
                                coverCrossUnsupported(
                                    fl, "Ignoring unsupported: malformed cover cross bin selection");
                                if (selectionsp) selectionsp->deleteTree();
                                return nullptr;
                            }
                            selection.binNames.push_back(binName);
                        }
                    }
                }
            } else {
                auto splitName = splitCoverCrossItemName(crossItemName(selp));
                selection.coverpointName = splitName.first;
                if (!splitName.second.empty()) selection.binNames.push_back(splitName.second);
            }
            if (selection.coverpointName.empty()) {
                coverCrossUnsupported(fl, "Ignoring unsupported: malformed cover cross bin selection");
                if (selectionsp) selectionsp->deleteTree();
                return nullptr;
            }
            if (CoverCrossSelection* const existingp = [&]() -> CoverCrossSelection* {
                    for (CoverCrossSelection& sel : clause.selections) {
                        if (sel.coverpointName == selection.coverpointName) return &sel;
                    }
                    return nullptr;
                }()) {
                if (!mergeCoverCrossSelection(*existingp, selection)) {
                    coverCrossUnsupported(
                        fl, "Ignoring unsupported: duplicate coverpoint selection in cover cross bin");
                    if (selectionsp) selectionsp->deleteTree();
                    return nullptr;
                }
                sawClauseItem = true;
                continue;
            }
            clause.selections.push_back(selection);
            sawClauseItem = true;
        }
        if (!finishClause()) {
            coverCrossUnsupported(fl, "Ignoring unsupported: malformed cover cross bin selection");
            if (selectionsp) selectionsp->deleteTree();
            return nullptr;
        }
        if (selectionsp) selectionsp->deleteTree();
        m_covercross.bins.push_back(std::move(spec));
        return nullptr;
    }
    void emitCoverCrossBin(FileLine* fl, AstVar* instVarp, AstVar* typeVarp, const string& crossName,
                           const string& binName, CoverBinKind kind, int binNum, AstNodeExpr* condp) {
        AstCoverOtherDecl* declp = nullptr;
        if (kind == CoverBinKind::NORMAL) {
            declp = new AstCoverOtherDecl{
                fl, "v_covergroup/" + m_covergroup.classp->name(), crossName + "." + binName, "",
                binNum};
            declp->hier(crossName + "." + binName);
            if (m_covercross.crossNumPrintMissing > 0) {
                declp->crossNumPrintMissing(m_covercross.crossNumPrintMissing);
            }
            m_covergroup.classp->addStmtsp(declp);
        }
        AstNode* bodysp = nullptr;
        if (kind == CoverBinKind::NORMAL) {
            AstMethodCall* const instHitp = new AstMethodCall{
                fl, new AstVarRef{fl, instVarp, VAccess::READWRITE}, "verilator_cov_hit",
                new AstArg{fl, "", newIntConst(fl, binNum)}};
            instHitp->dtypeSetVoid();
            AstMethodCall* const typeHitp = new AstMethodCall{
                fl, new AstVarRef{fl, typeVarp, VAccess::READWRITE}, "verilator_cov_hit",
                new AstArg{fl, "", newIntConst(fl, binNum)}};
            typeHitp->dtypeSetVoid();
            bodysp = instHitp->makeStmt();
            AstNode::addNext(bodysp, typeHitp->makeStmt());
            AstNode::addNext(bodysp, new AstCoverInc{fl, declp});
        } else if (kind == CoverBinKind::ILLEGAL) {
            bodysp = new AstDisplay{fl, VDisplayType::DT_ERROR,
                                    "Illegal cover bin hit: " + crossName + "." + binName, nullptr,
                                    nullptr};
        } else if (kind == CoverBinKind::IGNORE) {
            bodysp = new AstAssign{
                fl, new AstVarRef{fl, m_covergroup.methods.defaultIntVarp, VAccess::WRITE},
                new AstVarRef{fl, m_covergroup.methods.defaultIntVarp, VAccess::READ}};
        }
        if (!bodysp) {
            VL_DO_DANGLING(condp->deleteTree(), condp);
            return;
        }
        AstIf* const ifp = new AstIf{fl, condp, nullptr};
        ifp->addThensp(bodysp);
        m_covergroup.methods.sampleFuncp->addStmtsp(ifp);
    }
    AstNode* finishCoverCross() {
        if (!m_covercross.active) return nullptr;
        if (m_covercross.unsupported) {
            cleanupCoverCrossState();
            return nullptr;
        }
        FileLine* const fl = m_covercross.flp;
        AstVar* const instVarp
            = new AstVar{fl, VVarType::MEMBER, m_covercross.name, VFlagChildDType{},
                         createStdCrossDType(fl)};
        m_covergroup.classp->addMembersp(instVarp);
        AstVar* const typeVarp = new AstVar{
            fl, VVarType::MEMBER, "verilator_cov_type_" + m_covercross.name, VFlagChildDType{},
            createStdCrossDType(fl)};
        typeVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_covergroup.classp->addMembersp(typeVarp);
        int totalBins = 0;
        if (m_covercross.bins.empty()) {
            int64_t totalBins64 = 1;
            for (const CoverpointInfo* const infop : m_covercross.infos) totalBins64 *= infop->totalBins;
            if (totalBins64 <= 0 || totalBins64 > std::numeric_limits<int32_t>::max()) {
                fl->v3warn(V3ErrorCode::COVERIGN,
                           "Ignoring unsupported: cover cross auto bin count too large");
                cleanupCoverCrossState();
                return nullptr;
            }
            totalBins = static_cast<int>(totalBins64);
        } else {
            totalBins = 0;
            for (const CoverCrossBinSpec& bin : m_covercross.bins) {
                if (bin.kind == CoverBinKind::NORMAL) ++totalBins;
            }
        }
        m_covergroup.ctorp->addStmtsp(new AstIf{
            fl, new AstEq{fl, new AstVarRef{fl, typeVarp, VAccess::READ},
                          new AstConst{fl, AstConst::Null{}}},
            new AstAssign{fl, new AstVarRef{fl, typeVarp, VAccess::WRITE},
                          new AstNew{fl, new AstArg{fl, "", newIntConst(fl, totalBins)}}}});
        {
            AstArg* const argsp = new AstArg{fl, "", newIntConst(fl, totalBins)};
            AstNode::addNext(argsp,
                             new AstArg{fl, "", new AstVarRef{fl, typeVarp, VAccess::READ}});
            m_covergroup.ctorp->addStmtsp(
                new AstAssign{fl, new AstVarRef{fl, instVarp, VAccess::WRITE}, new AstNew{fl, argsp}});
        }
        m_covercross.crossNumPrintMissing
            = optionConstInt(m_covercross.options, "cross_num_print_missing", 0);
        for (CoverpointPendingOption& opt : m_covercross.options) {
            AstVar* const targetVarp = opt.typeOption ? typeVarp : instVarp;
            AstNodeExpr* valuep = opt.valuep;
            if (valuep && valuep->backp()) valuep = valuep->unlinkFrBack();
            m_covergroup.ctorp->addStmtsp(makeCoverageOptionAssign(
                opt.flp, new AstVarRef{opt.flp, targetVarp, VAccess::WRITE}, opt.typeOption,
                opt.member, valuep));
            opt.valuep = nullptr;
        }
        for (const string& member : {"weight"s, "goal"s, "comment"s}) {
            m_covergroup.ctorp->addStmtsp(makeCoverageOptionAssign(
                fl, new AstVarRef{fl, instVarp, VAccess::WRITE}, true, member,
                makeCoverpointMemberSel(
                    fl,
                    makeCoverpointMemberSel(fl, new AstVarRef{fl, typeVarp, VAccess::READ},
                                            "type_option", VAccess::READ),
                    member, VAccess::READ)));
        }
        if (m_covercross.bins.empty()) {
            std::vector<int> strides;
            strides.reserve(m_covercross.infos.size());
            int stride = totalBins;
            for (const CoverpointInfo* const infop : m_covercross.infos) {
                stride /= infop->totalBins;
                strides.push_back(stride);
            }
            for (int binNum = 0; binNum < totalBins; ++binNum) {
                AstNodeExpr* condp = m_covercross.iffp ? m_covercross.iffp->cloneTreePure(false) : nullptr;
                for (size_t i = 0; i < m_covercross.infos.size(); ++i) {
                    const CoverpointInfo* const infop = m_covercross.infos[i];
                    const int itemBinNum = (binNum / strides[i]) % infop->totalBins;
                    AstNodeExpr* const itemCondp = infop->bins[itemBinNum].condp->cloneTreePure(false);
                    condp = condp ? makeCoverLogAnd(fl, condp, itemCondp) : itemCondp;
                }
                emitCoverCrossBin(fl, instVarp, typeVarp, m_covercross.name,
                                  "__auto[" + cvtToStr(binNum) + "]", CoverBinKind::NORMAL, binNum,
                                  condp);
            }
        } else {
            int covBinNum = 0;
            for (const CoverCrossBinSpec& bin : m_covercross.bins) {
                AstNodeExpr* condp = nullptr;
                for (const CoverCrossClause& clause : bin.clauses) {
                    AstNodeExpr* clauseCondp
                        = m_covercross.iffp ? m_covercross.iffp->cloneTreePure(false) : nullptr;
                    if (bin.iffp) {
                        AstNodeExpr* const binIffp = bin.iffp->cloneTreePure(false);
                        clauseCondp = clauseCondp ? makeCoverLogAnd(bin.flp, clauseCondp, binIffp)
                                                  : binIffp;
                    }
                    if (clause.iffp) {
                        AstNodeExpr* const clauseIffp = clause.iffp->cloneTreePure(false);
                        clauseCondp = clauseCondp ? makeCoverLogAnd(bin.flp, clauseCondp, clauseIffp)
                                                  : clauseIffp;
                    }
                    for (const CoverpointInfo* const infop : m_covercross.infos) {
                        const CoverCrossSelection* const selectionp
                            = findCoverCrossSelection(clause, infop->name);
                        AstNodeExpr* itemCondp = makeCoverpointBinSelectCond(
                            bin.flp, *infop,
                            selectionp ? selectionp->binNames : std::vector<std::string>{},
                            selectionp ? selectionp->selectNone : false);
                        if (!itemCondp) {
                            fl->v3warn(V3ErrorCode::COVERIGN,
                                       "Ignoring unsupported: cover cross bin '" + bin.name
                                           + "' references unknown coverpoint/bin");
                            cleanupCoverCrossState();
                            return nullptr;
                        }
                        if (selectionp && selectionp->invert) {
                            itemCondp = makeCoverLogNot(bin.flp, itemCondp);
                        }
                        clauseCondp = clauseCondp ? makeCoverLogAnd(bin.flp, clauseCondp, itemCondp)
                                                  : itemCondp;
                    }
                    condp = condp ? makeCoverLogOr(bin.flp, condp, clauseCondp) : clauseCondp;
                }
                const int binNum = (bin.kind == CoverBinKind::NORMAL) ? covBinNum : -1;
                emitCoverCrossBin(bin.flp, instVarp, typeVarp, m_covercross.name, bin.name, bin.kind,
                                  binNum, condp);
                if (bin.kind == CoverBinKind::NORMAL) ++covBinNum;
            }
        }
        m_covergroup.coverpoints.emplace_back(
            CoverpointInfo{m_covercross.name, instVarp, typeVarp, nullptr, totalBins, {}});
        cleanupCoverCrossState();
        return nullptr;
    }
    void maybeAddCovergroupAutosample(AstVar* nodep) {
        if (insideClassDecl()) return;
        AstNodeDType* const dtypep = nodep ? nodep->dtypep() : nullptr;
        if (!dtypep) return;
        const AstNodeDType* baseDTypep = dtypep;
        if (!VN_IS(dtypep, RefDType) && !VN_IS(dtypep, ClassRefDType)) baseDTypep = dtypep->skipRefp();
        if (!baseDTypep) return;
        if (const CovergroupAutoSample* const autosp = findCovergroupAutosample(dtypep)) {
            AstMethodCall* const samplep = new AstMethodCall{
                nodep->fileline(), new AstVarRef{nodep->fileline(), nodep, VAccess::READ}, "sample",
                autosp->argsp ? static_cast<::AstArg*>(autosp->argsp->cloneTree(true)) : nullptr};
            samplep->dtypeSetVoid();
            AstIf* const ifp = new AstIf{
                nodep->fileline(),
                new AstNeq{nodep->fileline(), new AstVarRef{nodep->fileline(), nodep, VAccess::READ},
                           new AstConst{nodep->fileline(), AstConst::Null{}}},
                samplep->makeStmt()};
            if (!autosp->atatHooks.empty()) {
                AstNodeModule* const modp = currentModulep();
                for (const CovergroupState::AtAtHook& hook : autosp->atatHooks) {
                    V3CoverAtat::registerHook(
                        modp, hook.target, hook.begin, static_cast<AstNode*>(ifp->cloneTree(true)));
                }
                VL_DO_DANGLING(ifp->deleteTree(), ifp);
                return;
            }
            AstNode::addNext<AstNode, AstNode>(
                nodep, new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS,
                                     static_cast<::AstSenTree*>(autosp->sentreep->cloneTree(true)),
                                     ifp});
            return;
        }
        AstClass* classp = nullptr;
        if (const AstClassRefDType* const classRefp = VN_CAST(baseDTypep, ClassRefDType)) {
            classp = classRefp->classp();
            if (!classp) classp = findClassByName(unscopedName(classRefp->name()));
        } else if (const AstRefDType* const refp = VN_CAST(baseDTypep, RefDType)) {
            classp = findClassByName(refp->name());
            if (!classp) classp = findClassByName(unscopedName(refp->name()));
        }
        if (!classp) return;
        for (AstNode* memberp = classp->membersp(); memberp; memberp = memberp->nextp()) {
            AstVar* const cgVarp = VN_CAST(memberp, Var);
            if (!cgVarp) continue;
            const CovergroupAutoSample* const cgAutosp = findCovergroupAutosample(cgVarp->dtypep());
            if (!cgAutosp) continue;
            AstNodeExpr* const objRefp = new AstVarRef{nodep->fileline(), nodep, VAccess::READ};
            AstMemberSel* const cgCallRefp
                = new AstMemberSel{nodep->fileline(), objRefp->cloneTreePure(false), cgVarp};
            cgCallRefp->access(VAccess::READ);
            AstArg* argsp
                = cgAutosp->argsp ? static_cast<::AstArg*>(cgAutosp->argsp->cloneTree(true)) : nullptr;
            for (AstArg* argp = argsp; argp; argp = VN_AS(argp->nextp(), Arg)) {
                qualifyClassMemberRefs(argp->exprp(), objRefp->cloneTreePure(false), classp);
            }
            AstMethodCall* const samplep
                = new AstMethodCall{nodep->fileline(), cgCallRefp, "sample", argsp};
            samplep->dtypeSetVoid();
            AstNodeExpr* const objValidp
                = new AstNeq{nodep->fileline(), objRefp->cloneTreePure(false),
                             new AstConst{nodep->fileline(), AstConst::Null{}}};
            AstMemberSel* const cgCondRefp
                = new AstMemberSel{nodep->fileline(), objRefp->cloneTreePure(false), cgVarp};
            cgCondRefp->access(VAccess::READ);
            AstNodeExpr* const cgValidp
                = new AstNeq{nodep->fileline(), cgCondRefp,
                             new AstConst{nodep->fileline(), AstConst::Null{}}};
            AstIf* const ifp = new AstIf{nodep->fileline(),
                                         makeCoverLogAnd(nodep->fileline(), objValidp, cgValidp),
                                         samplep->makeStmt()};
            AstSenTree* const sentreep = static_cast<::AstSenTree*>(cgAutosp->sentreep->cloneTree(true));
            qualifyClassMemberRefs(sentreep, objRefp->cloneTreePure(false), classp);
            AstNode::addNext<AstNode, AstNode>(
                nodep, new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, sentreep, ifp});
        }
    }
    AstNodeDType* createStdCoverpointDType(FileLine* fl) {
        v3Global.setUsesStdPackage();
        return new AstRefDType{fl, "vl_coverpoint_t",
                               new AstClassOrPackageRef{fl, "std", nullptr, nullptr}, nullptr};
    }
    AstNodeDType* createStdCrossDType(FileLine* fl) {
        v3Global.setUsesStdPackage();
        return new AstRefDType{fl, "vl_cross_t",
                               new AstClassOrPackageRef{fl, "std", nullptr, nullptr}, nullptr};
    }
    AstNode* makeDirectOptionAssign(FileLine* fl, AstNodeExpr* fromp, const string& member,
                                    AstNodeExpr* valuep) {
        AstNodeExpr* const memberSelp = makeCoverpointMemberSel(fl, fromp, member, VAccess::WRITE);
        return new AstAssign{fl, memberSelp, valuep};
    }
    AstNode* makeCoverageOptionAssign(FileLine* fl, AstNodeExpr* fromp, bool typeOption,
                                      const string& member, AstNodeExpr* valuep) {
        AstNodeExpr* const optionSelp = makeCoverpointMemberSel(
            fl, fromp, typeOption ? "type_option" : "option", VAccess::WRITE);
        AstNodeExpr* const memberSelp = makeCoverpointMemberSel(fl, optionSelp, member, VAccess::WRITE);
        return new AstAssign{fl, memberSelp, valuep};
    }
    AstNode* coverageOptionAssign(FileLine* fl, const string& scopeName, const string& member,
                                  AstNodeExpr* valuep) {
        if (scopeName != "option" && scopeName != "type_option") {
            fl->v3error("Syntax error; expected 'option' or 'type_option': '" << scopeName << "'");
            VL_DO_DANGLING(valuep->deleteTree(), valuep);
            return nullptr;
        }
        const bool typeOption = scopeName == "type_option";
        if (m_coverpoint.active) {
            m_coverpoint.options.emplace_back(
                CoverpointPendingOption{fl, typeOption, member, valuep});
            return nullptr;
        }
        if (m_covercross.active) {
            if (!crossOptionMemberSupported(member, typeOption)) {
                coverCrossUnsupported(fl, "Ignoring unsupported: coverage cross option");
                VL_DO_DANGLING(valuep->deleteTree(), valuep);
                return nullptr;
            }
            m_covercross.options.emplace_back(
                CoverpointPendingOption{fl, typeOption, member, valuep});
            return nullptr;
        }
        if (!m_covergroup.active) return new AstCgOptionAssign{fl, typeOption, member, valuep};
        m_covergroup.options.emplace_back(CoverpointPendingOption{fl, typeOption, member, valuep});
        AstVar* const targetVarp
            = typeOption ? m_covergroup.methods.typeOptionVarp : m_covergroup.methods.optionVarp;
        m_covergroup.ctorp->addStmtsp(
            makeDirectOptionAssign(fl, new AstVarRef{fl, targetVarp, VAccess::WRITE}, member, valuep));
        return nullptr;
    }
    CoverGroupMethods createCoverGroupMethods(AstClass* nodep, AstNode* sampleArgs) {
        CoverGroupMethods methods;

        // IEEE: option
        {
            v3Global.setUsesStdPackage();
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MEMBER, "option", VFlagChildDType{},
                             new AstRefDType{nodep->fileline(), "vl_covergroup_options_t",
                                             new AstClassOrPackageRef{nodep->fileline(), "std",
                                                                      nullptr, nullptr},
                                             nullptr}};
            nodep->addMembersp(varp);
            methods.optionVarp = varp;
        }

        // IEEE: type_option
        {
            v3Global.setUsesStdPackage();
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MEMBER, "type_option", VFlagChildDType{},
                             new AstRefDType{nodep->fileline(), "vl_covergroup_type_options_t",
                                             new AstClassOrPackageRef{nodep->fileline(), "std",
                                                                      nullptr, nullptr},
                                             nullptr}};
            nodep->addMembersp(varp);
            methods.typeOptionVarp = varp;
        }

        // Hidden instance name storage for set_inst_name()
        {
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MEMBER, "verilator_cov_inst_name",
                             nodep->findStringDType()};
            nodep->addMembersp(varp);
            methods.instNameVarp = varp;
        }

        // Hidden type-level merge_instances mirror for static get_coverage().
        {
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MEMBER,
                             "verilator_cov_type_merge_instances", nodep->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            nodep->addMembersp(varp);
            methods.typeMergeInstancesVarp = varp;
        }

        // Hidden type-level instance counters for non-merged type coverage.
        {
            AstVar* const countVarp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                                 "verilator_cov_instance_count",
                                                 nodep->findIntDType()};
            countVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            nodep->addMembersp(countVarp);
            methods.instCountVarp = countVarp;

            AstVar* const sumVarp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                               "verilator_cov_instance_covered_sum",
                                               nodep->findIntDType()};
            sumVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            nodep->addMembersp(sumVarp);
            methods.instCoveredSumVarp = sumVarp;

            AstVar* const totalSumVarp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                                    "verilator_cov_instance_total_sum",
                                                    nodep->findIntDType()};
            totalSumVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            nodep->addMembersp(totalSumVarp);
            methods.instTotalSumVarp = totalSumVarp;
        }

        // Hidden per-instance aggregate covered-bin tracker.
        {
            AstVar* const varp
                = new AstVar{nodep->fileline(), VVarType::MEMBER,
                             "verilator_cov_instance_prev_covered", nodep->findIntDType()};
            nodep->addMembersp(varp);
            methods.instPrevCoveredVarp = varp;

            AstVar* const totalVarp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                                 "verilator_cov_instance_prev_total",
                                                 nodep->findIntDType()};
            nodep->addMembersp(totalVarp);
            methods.instPrevTotalVarp = totalVarp;
        }

        // Hidden scratch storage for synthesized no-op statements.
        {
            AstVar* const varp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                            "verilator_cov_dummy_int", nodep->findIntDType()};
            nodep->addMembersp(varp);
            methods.defaultIntVarp = varp;
        }

        // IEEE: function void sample()
        {
            AstFunc* const funcp = new AstFunc{nodep->fileline(), "sample", nullptr, nullptr};
            funcp->addStmtsp(sampleArgs);
            funcp->classMethod(true);
            funcp->dtypep(funcp->findVoidDType());
            nodep->addMembersp(funcp);
            methods.sampleFuncp = funcp;
        }

        // IEEE: function void start(), void stop()
        for (const string& name : {"start"s, "stop"s}) {
            AstFunc* const funcp = new AstFunc{nodep->fileline(), name, nullptr, nullptr};
            funcp->classMethod(true);
            funcp->dtypep(funcp->findVoidDType());
            nodep->addMembersp(funcp);
            if (name == "start") {
                methods.startFuncp = funcp;
            } else {
                methods.stopFuncp = funcp;
            }
        }

        // IEEE: static function real get_coverage(optional ref int, optional ref int)
        // IEEE: static function real get_type_coverage(optional ref int, optional ref int)
        // IEEE: function real get_inst_coverage(optional ref int, optional ref int)
        for (const string& name : {"get_coverage"s, "get_type_coverage"s, "get_inst_coverage"s}) {
            AstFunc* const funcp = new AstFunc{nodep->fileline(), name, nullptr, nullptr};
            funcp->fileline()->warnOff(V3ErrorCode::NORETURN, true);
            funcp->isStatic(name != "get_inst_coverage");
            funcp->classMethod(true);
            funcp->dtypep(funcp->findVoidDType());
            nodep->addMembersp(funcp);
            CoverGroupCoverageMethod* infop = nullptr;
            if (name == "get_coverage") {
                infop = &methods.typeCoverage;
            } else if (name == "get_type_coverage") {
                infop = &methods.typeCoverageAlias;
            } else {
                infop = &methods.instCoverage;
            }
            CoverGroupCoverageMethod& info = *infop;
            info.funcp = funcp;
            AstVar* const retVarp
                = new AstVar{nodep->fileline(), VVarType::MEMBER, name, nodep->findDoubleDType()};
            retVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            retVarp->funcLocal(true);
            retVarp->direction(VDirection::OUTPUT);
            retVarp->funcReturn(true);
            funcp->fvarp(retVarp);
            info.returnVarp = retVarp;
            AstVar* const coveredArgp = new AstVar{nodep->fileline(), VVarType::MEMBER,
                                                   "covered_bins", nodep->findIntDType()};
            coveredArgp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            coveredArgp->funcLocal(true);
            coveredArgp->direction(VDirection::REF);
            funcp->addStmtsp(coveredArgp);
            info.coveredBinsArgp = coveredArgp;
            AstVar* const totalArgp = new AstVar{nodep->fileline(), VVarType::MEMBER, "total_bins",
                                                 nodep->findIntDType()};
            totalArgp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            totalArgp->funcLocal(true);
            totalArgp->direction(VDirection::REF);
            funcp->addStmtsp(totalArgp);
            info.totalBinsArgp = totalArgp;
        }
        // IEEE: function void set_inst_name(string)
        {
            AstFunc* const funcp
                = new AstFunc{nodep->fileline(), "set_inst_name", nullptr, nullptr};
            funcp->classMethod(true);
            funcp->dtypep(funcp->findVoidDType());
            nodep->addMembersp(funcp);
            methods.setInstNameFuncp = funcp;
            AstVar* const varp = new AstVar{nodep->fileline(), VVarType::MEMBER, "name",
                                            nodep->findStringDType()};
            varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            varp->funcLocal(true);
            varp->direction(VDirection::INPUT);
            funcp->addStmtsp(varp);
            methods.setInstNameArgp = varp;
            funcp->addStmtsp(
                new AstAssign{nodep->fileline(),
                              new AstVarRef{nodep->fileline(), methods.instNameVarp, VAccess::WRITE},
                              new AstVarRef{nodep->fileline(), varp, VAccess::READ}});
        }
        return methods;
    }
    void cleanupCoverpointState() {
        if (m_coverpoint.exprp) VL_DO_DANGLING(m_coverpoint.exprp->deleteTree(), m_coverpoint.exprp);
        if (m_coverpoint.iffp) VL_DO_DANGLING(m_coverpoint.iffp->deleteTree(), m_coverpoint.iffp);
        for (CoverBinSpec& bin : m_coverpoint.bins) deleteCoverBinSpec(bin);
        for (CoverpointPendingOption& opt : m_coverpoint.options) {
            if (opt.valuep) VL_DO_DANGLING(opt.valuep->deleteTree(), opt.valuep);
        }
        m_coverpoint = CoverpointState{};
    }
    AstClass* beginCovergroup(FileLine* fl, const string& name, AstNode* ctorArgsp,
                              AstNode* coverageEventp) {
        m_covergroup = CovergroupState{};
        cleanupCoverCrossState();
        AstClass* const cgClassp = new AstClass{fl, name, V3ParseImp::parsep()->libname()};
        cgClassp->isCovergroup(true);
        AstFunc* const newp = new AstFunc{fl, "new", nullptr, nullptr};
        newp->fileline()->warnOff(V3ErrorCode::NORETURN, true);
        newp->classMethod(true);
        newp->isConstructor(true);
        newp->dtypep(cgClassp->dtypep());
        newp->addStmtsp(ctorArgsp);
        cgClassp->addMembersp(newp);
        m_covergroup.active = true;
        m_covergroup.classp = cgClassp;
        m_covergroup.ownerClassp = currentClassDeclp();
        m_covergroup.ctorp = newp;
        m_covergroup.ownerInClass = insideClassDecl();
        m_covergroup.methods = createCoverGroupMethods(cgClassp, nullptr);
        prepareCovergroupCtorBindings();
        enableCovergroupEventSampling(coverageEventp);
        return cgClassp;
    }
    AstNodeExpr* makeCovergroupWeightExpr(FileLine* fl, const CoverpointInfo& info,
                                          bool typeLevel) const {
        AstNodeExpr* const targetRefp
            = new AstVarRef{fl, typeLevel ? info.typeVarp : info.instVarp, VAccess::READ};
        AstNodeExpr* const optionSelp
            = makeCoverpointMemberSel(fl, targetRefp, typeLevel ? "type_option" : "option",
                                      VAccess::READ);
        return makeCoverpointMemberSel(fl, optionSelp, "weight", VAccess::READ);
    }
    AstNodeExpr* makeCovergroupBinsExpr(FileLine* fl, bool typeLevel, bool covered) const {
        const string method = covered ? "verilator_cov_covered_bins"s : "verilator_cov_total_bins"s;
        AstNodeExpr* sump = new AstConst{fl, 0};
        for (const CoverpointInfo& info : m_covergroup.coverpoints) {
            AstNodeExpr* itemp = nullptr;
            if (typeLevel) {
                AstNodeExpr* const typeRefp = new AstVarRef{fl, info.typeVarp, VAccess::READ};
                AstMethodCall* const callp
                    = new AstMethodCall{fl, new AstVarRef{fl, info.typeVarp, VAccess::READ}, method};
                AstNodeExpr* const checkp
                    = new AstNeq{fl, typeRefp, new AstConst{fl, AstConst::Null{}}};
                itemp = new AstCond{fl, checkp, callp, new AstConst{fl, 0}};
            } else {
                itemp = new AstMethodCall{fl, new AstVarRef{fl, info.instVarp, VAccess::READ}, method};
            }
            itemp = new AstMul{fl, itemp, makeCovergroupWeightExpr(fl, info, typeLevel)};
            sump = new AstAdd{fl, sump, itemp};
        }
        return sump;
    }
    void startCoverpoint(FileLine* fl, const string& name, AstNodeExpr* exprp, AstNodeExpr* iffp) {
        cleanupCoverpointState();
        m_coverpoint.active = true;
        m_coverpoint.flp = fl;
        std::string coverpointName = name;
        const std::string preBindCoverpointName
            = coverpointName.empty() ? defaultCoverpointName(exprp) : std::string{};
        if (!m_covergroup.eventDriven && !m_covergroup.extendsUnsupported) {
            exprp = VN_AS(bindNonEventCovergroupRefs(exprp), NodeExpr);
            iffp = VN_CAST(bindNonEventCovergroupRefs(iffp), NodeExpr);
        }
        if (coverpointName.empty()) coverpointName = preBindCoverpointName;
        if (coverpointName.empty()) coverpointName = defaultCoverpointName(exprp);
        if (coverpointName.empty()) {
            coverpointName = "verilator_cov_coverpoint" + cvtToStr(m_covergroup.autoCoverpointNum++);
        }
        m_coverpoint.name = coverpointName;
        if (m_covergroup.extendsUnsupported) {
            fl->v3warn(V3ErrorCode::COVERIGN, "Ignoring unsupported: covergroup extends");
            m_coverpoint.unsupported = true;
        }
        if (m_covergroup.eventDriven) {
            m_coverpoint.exprp = addHiddenCoverSampleArg(fl, "cg_expr_", exprp);
            m_coverpoint.iffp = iffp ? addHiddenCoverSampleArg(fl, "cg_iff_", iffp) : nullptr;
        } else {
            m_coverpoint.exprp = exprp;
            m_coverpoint.iffp = iffp;
        }
    }
    AstNode* addCoverpointBin(FileLine* fl, const string& name, AstNode* binsArrayp,
                              AstNodeExpr* valueItemsp, AstNodeExpr* withp, AstNodeExpr* iffp,
                              CoverBinKind kind, bool wildcard = false,
                              AstNodeExpr* withDomainExprp = nullptr,
                              bool defaultSequence = false) {
        if (!m_coverpoint.active) {
            if (binsArrayp) binsArrayp->deleteTree();
            if (valueItemsp) valueItemsp->deleteTree();
            if (withp) withp->deleteTree();
            if (iffp) iffp->deleteTree();
            if (withDomainExprp) withDomainExprp->deleteTree();
            return nullptr;
        }
        if (wildcard && valueItemsp && !wildcardValueItemsSupported(valueItemsp)) {
            fl->v3warn(V3ErrorCode::COVERIGN,
                       "Ignoring unsupported: cover bin 'wildcard' range specification");
            if (binsArrayp) binsArrayp->deleteTree();
            if (valueItemsp) valueItemsp->deleteTree();
            if (withp) withp->deleteTree();
            if (iffp) iffp->deleteTree();
            if (withDomainExprp) withDomainExprp->deleteTree();
            return nullptr;
        }
        AstNodeExpr* arraySizep = nullptr;
        bool unsizedArray = false;
        if (binsArrayp) {
            if (VN_IS(binsArrayp, Empty)) {
                unsizedArray = true;
                VL_DO_DANGLING(binsArrayp->deleteTree(), binsArrayp);
            } else {
                arraySizep = VN_AS(binsArrayp, NodeExpr);
            }
        }
        if ((unsizedArray || arraySizep) && !valueItemsp) {
            if (withp) {
                valueItemsp = makeFilteredCoverExprValueItems(fl, withp, withDomainExprp);
                if (valueItemsp && !VN_IS(valueItemsp, Const)) {
                    VL_DO_DANGLING(withp->deleteTree(), withp);
                    withp = nullptr;
                } else if (!valueItemsp) {
                    valueItemsp = makeCoverExprDomainValueItems(fl, withDomainExprp);
                }
            }
            if (!valueItemsp) {
                fl->v3warn(V3ErrorCode::COVERIGN,
                           "Ignoring unsupported: cover bin array 'with' specification");
                if (withp) withp->deleteTree();
                if (iffp) iffp->deleteTree();
                if (arraySizep) VL_DO_DANGLING(arraySizep->deleteTree(), arraySizep);
                if (withDomainExprp) withDomainExprp->deleteTree();
                return nullptr;
            }
        }
        if ((unsizedArray || arraySizep) && wildcard) {
            fl->v3warn(V3ErrorCode::COVERIGN,
                       "Ignoring unsupported: cover bin array 'wildcard' specification");
            if (valueItemsp) valueItemsp->deleteTree();
            if (withp) withp->deleteTree();
            if (iffp) iffp->deleteTree();
            if (arraySizep) VL_DO_DANGLING(arraySizep->deleteTree(), arraySizep);
            if (withDomainExprp) withDomainExprp->deleteTree();
            return nullptr;
        }
        if (withDomainExprp) VL_DO_DANGLING(withDomainExprp->deleteTree(), withDomainExprp);
        if (m_covergroup.eventDriven && iffp) iffp = addHiddenCoverSampleArg(fl, "cg_biniff_", iffp);
        m_coverpoint.bins.emplace_back(
            CoverBinSpec{fl,        name,     valueItemsp, nullptr, nullptr, withp, iffp, arraySizep,
                         kind,      CoverTransRepeatKind::NONE, 0,   0,       wildcard, false,
                         unsizedArray, defaultSequence, nullptr});
        return nullptr;
    }
    AstNode* addCoverpointTransitionBin(FileLine* fl, const string& name, AstNode* binsArrayp,
                                        AstNode* transItemsp, AstNodeExpr* iffp,
                                        CoverBinKind kind = CoverBinKind::NORMAL,
                                        bool wildcard = false) {
        if (!m_coverpoint.active) {
            if (binsArrayp) binsArrayp->deleteTree();
            if (transItemsp) transItemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return nullptr;
        }
        if (binsArrayp) {
            fl->v3warn(V3ErrorCode::COVERIGN, "Ignoring unsupported: cover bin transition variation");
            if (binsArrayp) binsArrayp->deleteTree();
            if (transItemsp) transItemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return nullptr;
        }
        std::vector<ParsedCoverTransStep> steps;
        if (!parseCoverTransitionSteps(fl, transItemsp, steps)) {
            fl->v3warn(V3ErrorCode::COVERIGN,
                       "Ignoring unsupported: cover bin transition repetition count");
            deleteParsedCoverTransSteps(steps);
            if (transItemsp) transItemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return nullptr;
        }
        if (wildcard) {
            for (const ParsedCoverTransStep& step : steps) {
                if (!step.valueItemsp || !wildcardValueItemsSupported(step.valueItemsp)) {
                    fl->v3warn(V3ErrorCode::COVERIGN,
                               "Ignoring unsupported: cover bin 'wildcard' range specification");
                    deleteParsedCoverTransSteps(steps);
                    if (transItemsp) transItemsp->deleteTree();
                    if (iffp) iffp->deleteTree();
                    return nullptr;
                }
            }
        }
        if (steps.size() == 1) {
            if (m_covergroup.eventDriven && iffp) iffp = addHiddenCoverSampleArg(fl, "cg_biniff_", iffp);
            const ParsedCoverTransStep& step = steps[0];
            if (step.repeatKind != CoverTransRepeatKind::NONE) {
                m_coverpoint.bins.emplace_back(CoverBinSpec{
                    fl,
                    name,
                    nullptr,
                    nullptr,
                    step.valueItemsp ? static_cast<AstNodeExpr*>(step.valueItemsp->cloneTree(true))
                                     : nullptr,
                    nullptr,
                    iffp,
                    nullptr,
                    kind,
                    step.repeatKind,
                    step.repeatMin,
                    step.repeatMax,
                    wildcard,
                    false,
                    false,
                    false,
                    nullptr});
            } else {
                m_coverpoint.bins.emplace_back(CoverBinSpec{
                    fl,
                    name,
                    step.valueItemsp ? static_cast<AstNodeExpr*>(step.valueItemsp->cloneTree(true))
                                     : nullptr,
                    nullptr,
                    nullptr,
                    nullptr,
                    iffp,
                    nullptr,
                    kind,
                    CoverTransRepeatKind::NONE,
                    0,
                    0,
                    wildcard,
                    false,
                    false,
                    false,
                    nullptr});
            }
            deleteParsedCoverTransSteps(steps);
            VL_DO_DANGLING(transItemsp->deleteTree(), transItemsp);
            return nullptr;
        }
        if (steps.size() != 2 || steps[0].repeatKind != CoverTransRepeatKind::NONE
            || steps[1].repeatKind != CoverTransRepeatKind::NONE) {
            fl->v3warn(V3ErrorCode::COVERIGN,
                       "Ignoring unsupported: cover bin transition sequence length");
            deleteParsedCoverTransSteps(steps);
            if (transItemsp) transItemsp->deleteTree();
            if (iffp) iffp->deleteTree();
            return nullptr;
        }
        deleteParsedCoverTransSteps(steps);
        if (m_covergroup.eventDriven && iffp) iffp = addHiddenCoverSampleArg(fl, "cg_biniff_", iffp);
        m_coverpoint.bins.emplace_back(CoverBinSpec{
            fl, name, nullptr, transItemsp, nullptr, nullptr, iffp, nullptr, kind,
            CoverTransRepeatKind::NONE, 0, 0, wildcard, true, false, false, nullptr});
        return nullptr;
    }
    void cleanupCovergroupCondTemplates() {
        for (CoverpointInfo& info : m_covergroup.coverpoints) deleteCoverpointInfoBins(info);
    }
    void populateCovergroupCoverageMethod(CoverGroupCoverageMethod& method, bool typeLevel) {
        AstFunc* const funcp = method.funcp;
        if (!funcp) return;
        FileLine* const fl = funcp->fileline();
        AstVar* const coveredAccp
            = new AstVar{fl, VVarType::MEMBER, "verilator_cov_covered_bins_acc",
                         funcp->findIntDType()};
        coveredAccp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        coveredAccp->funcLocal(true);
        funcp->addStmtsp(coveredAccp);
        AstVar* const totalAccp
            = new AstVar{fl, VVarType::MEMBER, "verilator_cov_total_bins_acc",
                         funcp->findIntDType()};
        totalAccp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        totalAccp->funcLocal(true);
        funcp->addStmtsp(totalAccp);
        funcp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, coveredAccp, VAccess::WRITE}, new AstConst{fl, 0}});
        funcp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, totalAccp, VAccess::WRITE}, new AstConst{fl, 0}});
        if (typeLevel) {
            AstNode* mergedSp = new AstAssign{
                fl, new AstVarRef{fl, coveredAccp, VAccess::WRITE},
                makeCovergroupBinsExpr(fl, true, true)};
            AstNode::addNext(
                mergedSp, new AstAssign{fl, new AstVarRef{fl, totalAccp, VAccess::WRITE},
                                        makeCovergroupBinsExpr(fl, true, false)});

            AstNode* avgSp = new AstAssign{
                fl, new AstVarRef{fl, coveredAccp, VAccess::WRITE},
                new AstVarRef{fl, m_covergroup.methods.instCoveredSumVarp, VAccess::READ}};
            AstNode::addNext(
                avgSp, new AstAssign{
                           fl, new AstVarRef{fl, totalAccp, VAccess::WRITE},
                           new AstVarRef{fl, m_covergroup.methods.instTotalSumVarp, VAccess::READ}});

            funcp->addStmtsp(
                new AstIf{fl,
                          new AstVarRef{fl, m_covergroup.methods.typeMergeInstancesVarp,
                                        VAccess::READ},
                          mergedSp, avgSp});
        } else {
            funcp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, coveredAccp, VAccess::WRITE},
                makeCovergroupBinsExpr(fl, false, true)});
            funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, totalAccp, VAccess::WRITE},
                                           makeCovergroupBinsExpr(fl, false, false)});
        }
        funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, method.coveredBinsArgp, VAccess::WRITE},
                                       new AstVarRef{fl, coveredAccp, VAccess::READ}});
        funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, method.totalBinsArgp, VAccess::WRITE},
                                       new AstVarRef{fl, totalAccp, VAccess::READ}});
        AstNodeExpr* const percentp
            = new AstDivD{fl,
                          new AstMulD{fl, new AstConst{fl, AstConst::RealDouble{}, 100.0},
                                      new AstIToRD{fl, new AstVarRef{fl, coveredAccp, VAccess::READ}}},
                          new AstIToRD{fl, new AstVarRef{fl, totalAccp, VAccess::READ}}};
        funcp->addStmtsp(new AstAssign{
            fl, new AstVarRef{fl, method.returnVarp, VAccess::WRITE},
            new AstCond{fl, new AstGt{fl, new AstVarRef{fl, totalAccp, VAccess::READ}, new AstConst{fl, 0}},
                        percentp, new AstConst{fl, AstConst::RealDouble{}, 100.0}}});
    }
    AstNode* finishCoverpoint() {
        if (!m_coverpoint.active) return nullptr;
        if (m_coverpoint.unsupported || !expandCoverpointBins()) {
            if (!m_coverpoint.unsupported) {
                m_coverpoint.flp->v3warn(
                    V3ErrorCode::COVERIGN,
                    "Ignoring unsupported: coverpoint auto bins or bin expansion");
            }
            cleanupCoverpointState();
            return nullptr;
        }
        detectCoverpointOverlaps();
        v3Global.setUsesStdPackage();
        FileLine* const fl = m_coverpoint.flp;
        AstVar* const instVarp = new AstVar{fl, VVarType::MEMBER, m_coverpoint.name, VFlagChildDType{},
                                            createStdCoverpointDType(fl)};
        m_covergroup.classp->addMembersp(instVarp);
        AstVar* const typeVarp
            = new AstVar{fl, VVarType::MEMBER, "verilator_cov_type_" + m_coverpoint.name,
                         VFlagChildDType{},
                         createStdCoverpointDType(fl)};
        typeVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_covergroup.classp->addMembersp(typeVarp);
        const bool hasTransition
            = std::any_of(m_coverpoint.bins.begin(), m_coverpoint.bins.end(),
                          [](const CoverBinSpec& bin) { return bin.transition; });
        const bool hasTransitionRepeat
            = std::any_of(m_coverpoint.bins.begin(), m_coverpoint.bins.end(), [](const CoverBinSpec& bin) {
                  return bin.transRepeatKind != CoverTransRepeatKind::NONE;
              });
        AstVar* prevVarp = nullptr;
        AstVar* prevValidVarp = nullptr;
        if (hasTransition) {
            AstNodeDType* const prevDTypep = inferCoverExprDType(fl, m_coverpoint.exprp);
            prevVarp
                = new AstVar{fl, VVarType::MEMBER, "verilator_cov_prev_" + m_coverpoint.name,
                             prevDTypep};
            m_covergroup.classp->addMembersp(prevVarp);
            prevValidVarp
                = new AstVar{fl, VVarType::MEMBER, "verilator_cov_prev_valid_" + m_coverpoint.name,
                             m_covergroup.methods.sampleFuncp->findBitDType()};
            m_covergroup.classp->addMembersp(prevValidVarp);
            m_coverpoint.prevVarp = prevVarp;
            m_coverpoint.prevValidVarp = prevValidVarp;
            m_covergroup.ctorp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, prevValidVarp, VAccess::WRITE}, new AstConst{fl, AstConst::BitFalse{}}});
        }

        int totalBins = 0;
        for (const CoverBinSpec& bin : m_coverpoint.bins) {
            if (bin.kind == CoverBinKind::NORMAL || bin.kind == CoverBinKind::DEFAULT) ++totalBins;
        }
        m_covergroup.ctorp->addStmtsp(new AstIf{
            fl, new AstEq{fl, new AstVarRef{fl, typeVarp, VAccess::READ},
                          new AstConst{fl, AstConst::Null{}}},
            new AstAssign{fl, new AstVarRef{fl, typeVarp, VAccess::WRITE},
                          new AstNew{fl, new AstArg{fl, "", newIntConst(fl, totalBins)}}}});
        {
            AstArg* const argsp = new AstArg{fl, "", newIntConst(fl, totalBins)};
            AstNode::addNext(argsp,
                             new AstArg{fl, "", new AstVarRef{fl, typeVarp, VAccess::READ}});
            m_covergroup.ctorp->addStmtsp(
                new AstAssign{fl, new AstVarRef{fl, instVarp, VAccess::WRITE}, new AstNew{fl, argsp}});
        }
        for (CoverpointPendingOption& opt : m_coverpoint.options) {
            AstVar* const targetVarp = opt.typeOption ? typeVarp : instVarp;
            AstNodeExpr* valuep = opt.valuep;
            if (valuep && valuep->backp()) valuep = valuep->unlinkFrBack();
            m_covergroup.ctorp->addStmtsp(makeCoverageOptionAssign(
                opt.flp, new AstVarRef{opt.flp, targetVarp, VAccess::WRITE}, opt.typeOption,
                opt.member, valuep));
            opt.valuep = nullptr;
        }
        for (const string& member : {"weight"s, "goal"s, "comment"s, "real_interval"s}) {
            m_covergroup.ctorp->addStmtsp(makeCoverageOptionAssign(
                fl, new AstVarRef{fl, instVarp, VAccess::WRITE}, true, member,
                makeCoverpointMemberSel(
                    fl,
                    makeCoverpointMemberSel(fl, new AstVarRef{fl, typeVarp, VAccess::READ},
                                            "type_option", VAccess::READ),
                    member, VAccess::READ)));
        }
        AstVar* const matchedVarp
            = new AstVar{fl, VVarType::MEMBER, "verilator_cov_matched_" + m_coverpoint.name,
                         m_covergroup.methods.sampleFuncp->findBitDType()};
        matchedVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        matchedVarp->funcLocal(true);
        addSampleVarDecl(matchedVarp);
        AstVar* const binIndexVarp
            = new AstVar{fl, VVarType::MEMBER, "verilator_cov_bin_index_" + m_coverpoint.name,
                         m_covergroup.methods.sampleFuncp->findIntDType()};
        binIndexVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        binIndexVarp->funcLocal(true);
        addSampleVarDecl(binIndexVarp);
        m_covergroup.methods.sampleFuncp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, matchedVarp, VAccess::WRITE},
                          new AstConst{fl, AstConst::BitFalse{}}});
        m_covergroup.methods.sampleFuncp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, binIndexVarp, VAccess::WRITE}, newIntConst(fl, -1)});
        int binNum = 0;
        std::vector<const CoverBinSpec*> defaultBins;
        AstNodeExpr* explicitMatchCondp = nullptr;
        std::vector<CoverpointBinInfo> crossBinInfos;
        for (CoverBinSpec& bin : m_coverpoint.bins) {
            if (bin.transRepeatKind != CoverTransRepeatKind::NONE) {
                AstVar* const countVarp
                    = new AstVar{bin.flp, VVarType::MEMBER,
                                 "verilator_cov_repeat_count_" + m_coverpoint.name + "_"
                                     + cvtToStr(binNum),
                                 m_covergroup.methods.sampleFuncp->findIntDType()};
                m_covergroup.classp->addMembersp(countVarp);
                m_covergroup.ctorp->addStmtsp(new AstAssign{
                    bin.flp, new AstVarRef{bin.flp, countVarp, VAccess::WRITE}, newIntConst(bin.flp, 0)});
                bin.transCountVarp = countVarp;
            }
            if (bin.kind == CoverBinKind::DEFAULT) {
                defaultBins.push_back(&bin);
                continue;
            }
            AstCoverOtherDecl* declp = nullptr;
            if (bin.kind == CoverBinKind::NORMAL) {
                declp = new AstCoverOtherDecl{bin.flp, "v_covergroup/" + m_covergroup.classp->name(),
                                              m_coverpoint.name + "." + bin.name, "", binNum};
                declp->hier(m_coverpoint.name + "." + bin.name);
                m_covergroup.classp->addStmtsp(declp);
            }
            AstNode* const actionp = makeCoverBinAction(bin, instVarp, typeVarp, declp, binNum);
            AstNodeExpr* const condp = makeCoverBinCond(bin);
            if (condp) {
                AstNodeExpr* const condClonep = condp->cloneTreePure(false);
                explicitMatchCondp = explicitMatchCondp
                                         ? makeCoverLogOr(bin.flp, explicitMatchCondp, condClonep)
                                         : condClonep;
            }
            AstIf* const ifp = new AstIf{bin.flp, condp, nullptr};
            ifp->addThensp(new AstAssign{bin.flp, new AstVarRef{bin.flp, matchedVarp, VAccess::WRITE},
                                         new AstConst{bin.flp, AstConst::BitTrue{}}});
                if (bin.kind == CoverBinKind::NORMAL) {
                    ifp->addThensp(new AstAssign{bin.flp,
                                                 new AstVarRef{bin.flp, binIndexVarp, VAccess::WRITE},
                                                 newIntConst(bin.flp, binNum)});
                    crossBinInfos.emplace_back(
                        CoverpointBinInfo{bin.name, binNum, condp->cloneTreePure(false),
                                          bin.valueItemsp ? bin.valueItemsp->cloneTreePure(true) : nullptr});
                }
            if (actionp) ifp->addThensp(actionp);
            m_covergroup.methods.sampleFuncp->addStmtsp(ifp);
            if (bin.kind == CoverBinKind::NORMAL) ++binNum;
        }
        for (const CoverBinSpec* binp : defaultBins) {
            AstCoverOtherDecl* const declp
                = new AstCoverOtherDecl{binp->flp, "v_covergroup/" + m_covergroup.classp->name(),
                                        m_coverpoint.name + "." + binp->name, "", binNum};
            declp->hier(m_coverpoint.name + "." + binp->name);
            m_covergroup.classp->addStmtsp(declp);
            AstNodeExpr* condp = nullptr;
            if (binp->defaultSequence && hasTransition && m_coverpoint.prevValidVarp) {
                AstNodeExpr* unmatchedp
                    = explicitMatchCondp
                          ? static_cast<AstNodeExpr*>(
                                new AstNot{binp->flp, explicitMatchCondp->cloneTreePure(false)})
                          : static_cast<AstNodeExpr*>(new AstConst{binp->flp, AstConst::BitTrue{}});
                condp = suppressGeneratedCoverageCondWarns(
                    new AstAnd{binp->flp,
                               new AstVarRef{binp->flp, m_coverpoint.prevValidVarp, VAccess::READ},
                               unmatchedp});
            } else {
                condp = new AstNot{binp->flp,
                                   new AstVarRef{binp->flp, matchedVarp, VAccess::READ}};
            }
            if (m_coverpoint.iffp) {
                condp = makeCoverLogAnd(
                    binp->flp,
                    suppressGeneratedCoverageCondWarns(m_coverpoint.iffp->cloneTreePure(false)),
                    condp);
            }
            if (binp->iffp) {
                condp = makeCoverLogAnd(
                    binp->flp, suppressGeneratedCoverageCondWarns(binp->iffp->cloneTreePure(false)),
                    condp);
            }
            AstIf* const ifp = new AstIf{binp->flp, condp, nullptr};
            ifp->addThensp(new AstAssign{binp->flp, new AstVarRef{binp->flp, matchedVarp, VAccess::WRITE},
                                         new AstConst{binp->flp, AstConst::BitTrue{}}});
            ifp->addThensp(new AstAssign{binp->flp,
                                         new AstVarRef{binp->flp, binIndexVarp, VAccess::WRITE},
                                         newIntConst(binp->flp, binNum)});
            ifp->addThensp(makeCoverBinAction(*binp, instVarp, typeVarp, declp, binNum));
            m_covergroup.methods.sampleFuncp->addStmtsp(ifp);
            ++binNum;
        }
        if (explicitMatchCondp) VL_DO_DANGLING(explicitMatchCondp->deleteTree(), explicitMatchCondp);
        if (hasTransitionRepeat) {
            for (const CoverBinSpec& bin : m_coverpoint.bins) {
                if (bin.transRepeatKind == CoverTransRepeatKind::NONE || !bin.transCountVarp
                    || !bin.transRepeatValueItemsp) {
                    continue;
                }
                AstNodeExpr* const matchp = makeCoverValueMatchCond(
                    bin.flp, m_coverpoint.exprp, bin.transRepeatValueItemsp, bin.wildcard);
                if (!matchp) continue;
                AstNodeExpr* nextCountp = nullptr;
                if (bin.transRepeatKind == CoverTransRepeatKind::CONSEC) {
                    nextCountp = new AstCond{
                        bin.flp, matchp,
                        new AstAdd{bin.flp,
                                   new AstVarRef{bin.flp, bin.transCountVarp, VAccess::READ},
                                   newIntConst(bin.flp, 1)},
                        newIntConst(bin.flp, 0)};
                } else {
                    nextCountp = new AstCond{
                        bin.flp, matchp,
                        new AstAdd{bin.flp,
                                   new AstVarRef{bin.flp, bin.transCountVarp, VAccess::READ},
                                   newIntConst(bin.flp, 1)},
                        new AstVarRef{bin.flp, bin.transCountVarp, VAccess::READ}};
                }
                AstNode* updatep = new AstAssign{
                    bin.flp, new AstVarRef{bin.flp, bin.transCountVarp, VAccess::WRITE}, nextCountp};
                if (AstNodeExpr* const enablep = makeCoverBinSampleEnableCond(bin)) {
                    m_covergroup.methods.sampleFuncp->addStmtsp(new AstIf{bin.flp, enablep, updatep});
                } else {
                    m_covergroup.methods.sampleFuncp->addStmtsp(updatep);
                }
            }
        }
        if (hasTransition) {
            AstNode* updatesp = new AstAssign{
                fl, new AstVarRef{fl, prevVarp, VAccess::WRITE}, m_coverpoint.exprp->cloneTreePure(false)};
            AstNode::addNext(
                updatesp,
                new AstAssign{fl, new AstVarRef{fl, prevValidVarp, VAccess::WRITE},
                              new AstConst{fl, AstConst::BitTrue{}}});
            if (m_coverpoint.iffp) {
                m_covergroup.methods.sampleFuncp->addStmtsp(
                    new AstIf{fl,
                              suppressGeneratedCoverageCondWarns(
                                  m_coverpoint.iffp->cloneTreePure(false)),
                              updatesp});
            } else {
                m_covergroup.methods.sampleFuncp->addStmtsp(updatesp);
            }
        }
        eraseCoverpointInfo(m_covergroup.coverpoints, m_coverpoint.name);
        m_covergroup.coverpoints.emplace_back(CoverpointInfo{
            m_coverpoint.name, instVarp, typeVarp, binIndexVarp, totalBins, std::move(crossBinInfos)});
        cleanupCoverpointState();
        return nullptr;
    }
    AstClass* finishCovergroup() {
        if (m_covergroup.extendsUnsupported) {
            cleanupCoverpointState();
            cleanupCoverCrossState();
            cleanupCovergroupCondTemplates();
            AstClass* const outp = m_covergroup.classp;
            m_covergroup = CovergroupState{};
            return outp;
        }
        finishCoverpoint();
        cleanupCoverCrossState();
        {
            FileLine* const fl = m_covergroup.classp->fileline();
            m_covergroup.ctorp->addStmtsp(
                new AstAssign{fl,
                              new AstVarRef{fl, m_covergroup.methods.instPrevCoveredVarp,
                                            VAccess::WRITE},
                              newIntConst(fl, 0)});
            m_covergroup.ctorp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, m_covergroup.methods.instCountVarp, VAccess::WRITE},
                new AstAdd{fl, new AstVarRef{fl, m_covergroup.methods.instCountVarp, VAccess::READ},
                           newIntConst(fl, 1)}});
            m_covergroup.ctorp->addStmtsp(
                new AstAssign{
                    fl,
                    new AstVarRef{fl, m_covergroup.methods.typeMergeInstancesVarp, VAccess::WRITE},
                    makeCoverpointMemberSel(
                        fl, new AstVarRef{fl, m_covergroup.methods.typeOptionVarp, VAccess::READ},
                        "merge_instances", VAccess::READ)});

            AstVar* const currentCoveredVarp
                = new AstVar{fl, VVarType::MEMBER, "verilator_cov_current_covered_bins",
                             m_covergroup.methods.sampleFuncp->findIntDType()};
            currentCoveredVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            currentCoveredVarp->funcLocal(true);
            addSampleVarDecl(currentCoveredVarp);
            AstVar* const currentTotalVarp
                = new AstVar{fl, VVarType::MEMBER, "verilator_cov_current_total_bins",
                             m_covergroup.methods.sampleFuncp->findIntDType()};
            currentTotalVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            currentTotalVarp->funcLocal(true);
            addSampleVarDecl(currentTotalVarp);
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, currentCoveredVarp, VAccess::WRITE},
                makeCovergroupBinsExpr(fl, false, true)});
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, currentTotalVarp, VAccess::WRITE},
                makeCovergroupBinsExpr(fl, false, false)});
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, m_covergroup.methods.instCoveredSumVarp, VAccess::WRITE},
                new AstAdd{
                    fl,
                    new AstVarRef{fl, m_covergroup.methods.instCoveredSumVarp, VAccess::READ},
                    new AstSub{
                        fl, new AstVarRef{fl, currentCoveredVarp, VAccess::READ},
                        new AstVarRef{fl, m_covergroup.methods.instPrevCoveredVarp, VAccess::READ}}}});
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, m_covergroup.methods.instTotalSumVarp, VAccess::WRITE},
                new AstAdd{
                    fl,
                    new AstVarRef{fl, m_covergroup.methods.instTotalSumVarp, VAccess::READ},
                    new AstSub{
                        fl, new AstVarRef{fl, currentTotalVarp, VAccess::READ},
                        new AstVarRef{fl, m_covergroup.methods.instPrevTotalVarp, VAccess::READ}}}});
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl,
                new AstVarRef{fl, m_covergroup.methods.instPrevCoveredVarp, VAccess::WRITE},
                new AstVarRef{fl, currentCoveredVarp, VAccess::READ}});
            m_covergroup.methods.sampleFuncp->addStmtsp(new AstAssign{
                fl,
                new AstVarRef{fl, m_covergroup.methods.instPrevTotalVarp, VAccess::WRITE},
                new AstVarRef{fl, currentTotalVarp, VAccess::READ}});
        }
        {
            FileLine* const ctorFl = m_covergroup.ctorp->fileline();
            m_covergroup.ctorp->addStmtsp(new AstAssign{
                ctorFl,
                new AstVarRef{ctorFl, m_covergroup.methods.instPrevTotalVarp, VAccess::WRITE},
                makeCovergroupBinsExpr(ctorFl, false, false)});
            m_covergroup.ctorp->addStmtsp(new AstAssign{
                ctorFl,
                new AstVarRef{ctorFl, m_covergroup.methods.instTotalSumVarp, VAccess::WRITE},
                new AstAdd{
                    ctorFl,
                    new AstVarRef{ctorFl, m_covergroup.methods.instTotalSumVarp, VAccess::READ},
                    new AstVarRef{ctorFl, m_covergroup.methods.instPrevTotalVarp, VAccess::READ}}});
        }
        populateCovergroupCoverageMethod(m_covergroup.methods.typeCoverage, true);
        populateCovergroupCoverageMethod(m_covergroup.methods.typeCoverageAlias, true);
        populateCovergroupCoverageMethod(m_covergroup.methods.instCoverage, false);
        if (m_covergroup.eventDriven) {
            const CovergroupAutoSample autosample{
                m_covergroup.eventSenTreep
                    ? static_cast<::AstSenTree*>(m_covergroup.eventSenTreep->cloneTree(true))
                    : nullptr,
                m_covergroup.autoSampleArgsp
                    ? static_cast<::AstArg*>(m_covergroup.autoSampleArgsp->cloneTree(true))
                    : nullptr,
                m_covergroup.methods.sampleFuncp,
                m_covergroup.atatHooks};
            m_covergroupAutoSamples[m_covergroup.classp->name()] = autosample;
            const string shortName = unscopedName(m_covergroup.classp->name());
            if (!shortName.empty() && shortName != m_covergroup.classp->name()) {
                m_covergroupAutoSamples[shortName] = CovergroupAutoSample{
                    autosample.sentreep
                        ? static_cast<::AstSenTree*>(autosample.sentreep->cloneTree(true))
                        : nullptr,
                    autosample.argsp ? static_cast<::AstArg*>(autosample.argsp->cloneTree(true))
                                     : nullptr,
                    autosample.sampleFuncp,
                    autosample.atatHooks};
            }
        } else if (m_covergroup.autoSampleArgsp) {
            m_covergroupImplicitSampleArgs[m_covergroup.classp->name()]
                = static_cast<::AstArg*>(m_covergroup.autoSampleArgsp->cloneTree(true));
            const string shortName = unscopedName(m_covergroup.classp->name());
            if (!shortName.empty() && shortName != m_covergroup.classp->name()) {
                m_covergroupImplicitSampleArgs[shortName]
                    = static_cast<::AstArg*>(m_covergroup.autoSampleArgsp->cloneTree(true));
            }
        }
        AstClass* const outp = m_covergroup.classp;
        clearPendingOptions(m_covergroup.options);
        cleanupCovergroupCondTemplates();
        m_covergroup = CovergroupState{};
        return outp;
    }
    AstDisplay* createDisplayError(FileLine* fileline) {
        AstDisplay* nodep = new AstDisplay{fileline, VDisplayType::DT_ERROR, "", nullptr, nullptr};
        AstNode::addNext<AstNode, AstNode>(nodep, new AstStop{fileline, false});
        return nodep;
    }
    AstNodeExpr* createGatePin(AstNodeExpr* exprp) {
        AstRange* const rangep = m_gateRangep;
        if (!rangep) {
            return exprp;
        } else {
            return new AstGatePin{rangep->fileline(), exprp, rangep->cloneTree(true)};
        }
    }
    AstSenTree* createSenTreeChanged(FileLine* fl, AstNodeExpr* exprp) {
        return new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_CHANGED, exprp}};
    }
    AstSenTree* createSenTreeDotStar(FileLine* fl) {
        return new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_COMBO_STAR, nullptr}};
    }
    AstNodeExpr* createGlobalClockParseRef(FileLine* fl) {
        return new AstParseRef{fl, "__024global_clock", nullptr, nullptr};
    }
    AstSenTree* createGlobalClockSenTree(FileLine* fl) {
        return createSenTreeChanged(fl, createGlobalClockParseRef(fl));
    }
    AstNode* createNettype(FileLine* fl, const string& name) {
        // As nettypes are unsupported, we just alias to logic
        AstTypedef* const nodep = new AstTypedef{fl, name, nullptr, VFlagChildDType{},
                                                 new AstBasicDType{fl, VFlagLogicPacked{}, 1}};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    AstNode* createTypedef(FileLine* fl, const string& name, AstNode* attrsp, AstNodeDType* basep,
                           AstNodeRange* rangep) {
        AstTypedef* const nodep = new AstTypedef{fl, name, attrsp, VFlagChildDType{},
                                                 singletonp()->createArray(basep, rangep, false)};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    AstNode* createTypedefFwd(FileLine* fl, const string& name, const VFwdType& fwdType) {
        AstTypedefFwd* const nodep = new AstTypedefFwd{fl, name, fwdType};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    void endLabel(FileLine* fl, const AstNode* nodep, const string* endnamep) {
        endLabel(fl, nodep->prettyName(), endnamep);
    }
    void endLabel(FileLine* fl, const string& name, const string* endnamep) {
        if (fl && endnamep && *endnamep != "" && name != *endnamep
            && name != AstNode::prettyName(*endnamep)) {
            fl->v3warn(ENDLABEL, "End label '" << *endnamep << "' does not match begin label '"
                                               << name << "'");
        }
    }
    void setDType(AstNodeDType* dtypep) {
        if (m_varDTypep) {
            UASSERT_OBJ(!m_varDTypep->backp(), m_varDTypep, "Should not link directly");
            VL_DO_CLEAR(m_varDTypep->deleteTree(), m_varDTypep = nullptr);
        }
        m_varDTypep = dtypep;
    }
    void setNetDelay(AstDelay* netDelayp) {
        if (m_netDelayp) {
            UASSERT_OBJ(!m_netDelayp->backp(), m_netDelayp, "Should not link directly");
            VL_DO_CLEAR(m_netDelayp->deleteTree(), m_netDelayp = nullptr);
        }
        m_netDelayp = netDelayp;
    }
    void setNetStrength(AstStrengthSpec* netStrengthp) { m_netStrengthp = netStrengthp; }
    void pinPush() {
        m_pinStack.push(m_pinNum);
        m_pinNum = 1;
    }
    void pinPop(FileLine* fl) {
        if (VL_UNCOVERABLE(m_pinStack.empty())) fl->v3fatalSrc("Underflow of pin stack");
        m_pinNum = m_pinStack.top();
        m_pinStack.pop();
    }
    AstNodeDType* addRange(AstBasicDType* dtypep, AstNodeRange* rangesp, bool isPacked) {
        // If dtypep isn't basic, don't use this, call createArray() instead
        if (!rangesp) {
            return dtypep;
        } else {
            // If rangesp is "wire [3:3][2:2][1:1] foo [5:5][4:4]"
            // then [1:1] becomes the basicdtype range; everything else is arraying
            // the final [5:5][4:4] will be passed in another call to createArray
            AstNodeRange* rangearraysp = nullptr;
            if (dtypep->isRanged()) {
                rangearraysp = rangesp;  // Already a range; everything is an array
            } else {
                AstNodeRange* finalp = rangesp;
                while (finalp->nextp()) finalp = VN_CAST(finalp->nextp(), Range);
                if (finalp != rangesp) {
                    finalp->unlinkFrBack();
                    rangearraysp = rangesp;
                }
                if (AstRange* const finalRangep = VN_CAST(finalp, Range)) {  // not an UnsizedRange
                    if (dtypep->implicit()) {
                        // It's no longer implicit but a wire logic type
                        AstBasicDType* const newp = new AstBasicDType{
                            dtypep->fileline(), VBasicDTypeKwd::LOGIC, dtypep->numeric(),
                            dtypep->width(), dtypep->widthMin()};
                        VL_DO_DANGLING(dtypep->deleteTree(), dtypep);
                        dtypep = newp;
                    }
                    dtypep->rangep(finalRangep);
                }
            }
            return createArray(dtypep, rangearraysp, isPacked);
        }
    }
    string unquoteString(FileLine* fileline, const std::string& text) VL_MT_DISABLED;
    void checkDpiVer(FileLine* fileline, const string& str) {
        if (str != "DPI-C" && !v3Global.opt.bboxSys())
            fileline->v3warn(E_UNSUPPORTED, "Unsupported DPI type '"
                                                << str
                                                << "': Use 'DPI-C' (IEEE 1800-2023 35.5.4)");
    }
    // Given a list of clocking declarations, put them in clocking items
    AstClockingItem* makeClockingItemList(FileLine* flp, const VDirection direction,
                                          AstNodeExpr* skewp, AstNode* const clockingDeclps) {
        AstClockingItem* itemsp = nullptr;
        for (AstNode *nodep = clockingDeclps, *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (nextp) nextp->unlinkFrBackWithNext();
            if (itemsp && skewp) skewp = skewp->cloneTree(false);
            AstClockingItem* itemp = new AstClockingItem{flp, direction, skewp, nodep};
            itemsp = AstNode::addNextNull(itemsp, itemp);
        }
        return itemsp;
    }

    void setScopedSigAttr(AstNode* attrsp) {
        if (m_scopedSigAttr) {  // clearing set attribute
            UASSERT_OBJ(!m_scopedSigAttr->backp(), m_scopedSigAttr, "Should not link directly");
            VL_DO_DANGLING(m_scopedSigAttr->deleteTree(), m_scopedSigAttr);
        }
        m_scopedSigAttr = attrsp;
    }

    void createScopedSigAttr(VAttrType vattrT) {
        setScopedSigAttr(new AstAttrOf{V3ParseImp::parsep()->lexFileline(), vattrT});
    }

    AstNode* cloneScopedSigAttr() const {
        return m_scopedSigAttr ? m_scopedSigAttr->cloneTree(true) : nullptr;
    }

    void createGenericIface(AstNode* const nodep, AstNodeRange* const rangep,
                            AstNode* sigAttrListp, FileLine* const modportFileline = nullptr,
                            const string& modportstrp = "") {
        m_varDecl = VVarType::GPARAM;
        m_varIO = VDirection::NONE;
        setDType(new AstParseTypeDType{nodep->fileline(), VFwdType::GENERIC_INTERFACE});
        m_varDeclTyped = true;
        const std::string uniqueName = "__VGIfaceParam" + nodep->name();
        AstNode::addNext(nodep,
                         createVariable(nodep->fileline(), uniqueName, rangep, sigAttrListp));
        m_varDecl = VVarType::IFACEREF;
        AstIfaceGenericDType* const refdtypep
            = new AstIfaceGenericDType{nodep->fileline(), modportFileline, modportstrp};
        setDType(refdtypep);
        m_varDeclTyped = true;
        m_varIO = VDirection::INPUT;
        AstNode::addNext(nodep,
                         createVariable(nodep->fileline(), nodep->name(), rangep, sigAttrListp));
        m_varDecl = VVarType::VAR;
    }

    // Wrap all statements in the given list in an AstBegin (except those already an AstBegin)
    static AstBegin* wrapInBegin(AstNodeStmt* stmtsp) {
        AstBegin* resp = nullptr;
        for (AstNodeStmt *nodep = stmtsp, *nextp; nodep; nodep = nextp) {
            nextp = VN_AS(nodep->nextp(), NodeStmt);
            if (nextp) nextp->unlinkFrBackWithNext();
            AstBegin* beginp = VN_CAST(nodep, Begin);
            if (!beginp) beginp = new AstBegin{nodep->fileline(), "", nodep, true};
            resp = AstNode::addNext(resp, beginp);
        }
        return resp;
    }
};
