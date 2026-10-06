// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hierarchical Verilation for large designs
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
// Hierarchical Verilation is useful for large designs.
// It reduces
//   - time and memory for Verilation
//   - compilation time especially when a hierarchical block is used many times
//
// Hierarchical Verilation internally uses --lib-create for each
// hierarchical block.  Upper modules read the wrapper from --lib-create
// instead of the Verilog design.
//
// Hierarchical Verilation runs as the following step
// 1) Find modules marked by /*verilator hier_block*/ metacomment
// 2) Generate ${prefix}_hier.mk to create protected-lib for hierarchical blocks and
//    final Verilation to process the top module, that refers wrappers
// 3) Call child Verilator process via ${prefix}_hier.mk
//
// There are 3 kinds of Verilator run.
// a) To create ${prefix}_hier.mk (--hierarchical)
// b) To --lib-create on each hierarchical block (--hierarchical-child)
// c) To load wrappers and Verilate the top module (... what primary flags?)
//
// Then user can build Verilated module as usual.
//
// Here is more detailed internal process.
// 1) Parser adds VPragmaType::HIER_BLOCK of AstPragma to modules
//    that are marked with /*verilator hier_block*/ metacomment in Verilator run a).
// 2) If module type parameters are present, V3Control marks hier param modules
// (marked with hier_params verilator config pragma) as modp->hierParams(true).
// This is done in run b), de-parameterized modules are mapped with their params one-to-one.
// 3) AstModule with HIER_BLOCK pragma is marked modp->hierBlock(true)
//    in V3LinkResolve.cpp during run a).
// 4) In V3LinkCells.cpp, the following things are done during run b) and c).
//    4-1) Delete the upper modules of the hierarchical block because the top module in run b) is
//         hierarchical block, not the top module of run c).
//    4-2) If the top module of the run b) or c) instantiates other hierarchical blocks that is
//         parameterized,
//         module and task names are renamed to the original name to be compatible with the
//         hier module to be called.
//
//         Parameterized modules have unique name by V3Param.cpp. The unique name contains '__' and
//         Verilator encodes '__' when loading such symbols.
// 5) In V3LinkDot.cpp,
//    5-1) Dotted access across hierarchical block boundary is checked. Access INTO a
//    hierarchical block (reaching one of its non-port symbols from outside) is not
//    supported. A reference OUT of one is supported: run a) detects it and promotes it
//    to a port, threaded to the block boundary - see promoteXmrPorts/bindXmrPorts at the
//    end of this file. Cases that cannot be modelled exactly (a width not known before
//    elaboration, a write, or a nested hierarchical block) are refused, never guessed.
//    5-2) If present, parameters in hier params module replace parameter values of
//    de-parameterized module in run b).
// 6) In V3Dead.cpp, some parameters of parameterized modules are protected not to be deleted even
//    if the parameter is not referred. This protection is necessary to match step 6) below.
// 7) In V3Param.cpp, use --lib-create wrapper of the parameterized module made in b) and c).
//    If a hierarchical block is a parameterized module and instantiated in multiple locations,
//    all parameters must exactly match.
// 8) In V3HierBlock.cpp, relationships among hierarchical blocks are checked in run a).
//    (which block uses other blocks..)
// 9) In V3EmitMk.cpp, ${prefix}_hier.mk is created in run a).
//
// There are three hidden command options:
//   --hierarchical-child is added to Verilator run b).
//   --hierarchical-block module_name,mangled_name,name0,value0,name1,value1,...
//       module_name  :The original modulename
//       mangled_name :Mangled name of parameterized modules (named in V3Param.cpp).
//                     Same as module_name for non-parameterized hierarchical block.
//       name         :The name of the parameter
//       value        :Overridden value of the parameter
//
//       Used for b) and c).
//       These options are repeated for all instantiated hierarchical blocks.
//   --hierarchical-params-file filename
//      filename    :Name of a hierarchical parameters file
//
//      Added in a), used for b).
//      Each de-parameterized module version has exactly one hier params file specified.

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3HierBlock.h"

#include "V3Container.h"
#include "V3Control.h"
#include "V3EmitV.h"
#include "V3File.h"
#include "V3Os.h"
#include "V3Stats.h"
#include "V3String.h"

#include <algorithm>
#include <cctype>
#include <memory>
#include <sstream>
#include <unordered_map>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

static string V3HierCommandArgsFilename(const string& prefix, bool forMkJson) {
    return v3Global.opt.makeDir() + "/" + prefix
           + (forMkJson ? "__hierMkJsonArgs.f" : "__hierMkArgs.f");
}

static string V3HierParametersFileName(const string& prefix) {
    return v3Global.opt.makeDir() + "/" + prefix + "__hierParameters.v";
}

static void V3HierWriteCommonInputs(const V3HierBlock* hblockp, std::ostream* of, bool forMkJson) {
    const string topModuleFile = hblockp ? hblockp->vFileIfNecessary() : "";
    if (!forMkJson) {
        for (const string& filename : V3HierGraph::sourceFiles(topModuleFile))
            *of << filename << "\n";
    }
    for (const auto& i : v3Global.opt.libraryFiles()) {
        if (V3Os::filenameRealPath(i.filename()) != topModuleFile)
            *of << "-v " << i.filename() << "\n";
    }
}

//######################################################################

bool V3HierBlock::stringParamPassable(const string& value) {
    // stringifyParams writes string values in double quotes into the arguments file, which
    // V3Options::parseOptsFile reads by lines, removing '/*' comments, and '//' comments after
    // whitespace, before splitting the quoted arguments. AstConst::parseParamLiteral for -G,
    // and V3HierarchicalBlockOption, then end each value at the next double quote.
    if (value.find_first_of("\n\"") != string::npos) return false;
    if (value.find("/*") != string::npos) return false;
    for (size_t pos = value.find("//"); pos != string::npos; pos = value.find("//", pos + 1)) {
        if (pos > 0 && std::isspace(static_cast<unsigned char>(value[pos - 1]))) return false;
    }
    return true;
}

V3HierBlock::StrGParams V3HierBlock::stringifyParams(const std::vector<AstVar*>& gparams,
                                                     bool forGOption) {
    StrGParams strParams;
    for (const AstVar* const gparam : gparams) {
        if (const AstConst* const constp = VN_CAST(gparam->valuep(), Const)) {
            string s;
            // Only constant parameter needs to be set to -G because already checked in
            // V3Param.cpp. See also ParamVisitor::checkSupportedParam() in the file.
            if (constp->isDouble()) {
                // 64 bit width of hex can be expressed with 16 chars.
                // 32 chars must be long enough for hexadecimal floating point
                // considering prefix of '0x', '.', and 'P'.
                std::vector<char> hexFpStr(32, '\0');
                const int len = VL_SNPRINTF(hexFpStr.data(), hexFpStr.size(), "%a",
                                            constp->num().toDouble());
                UASSERT_OBJ(0 < len && static_cast<size_t>(len) < hexFpStr.size(), constp,
                            " is not properly converted to string");
                s = hexFpStr.data();
            } else if (constp->isString()) {
                s = constp->num().toString();
                if (!forGOption) s = VString::quoteBackslash(s);
                s = VString::quoteStringLiteralForShell(s);
            } else {  // Either signed or unsigned integer.
                // Constant folding can leave the signedness on the dtype, not the V3Number.
                V3Number num{constp->num()};
                num.isSigned(constp->isSigned());
                s = num.ascii(true, true);
                s = VString::quoteAny(s, '\'', '\\');
            }
            strParams.emplace_back(gparam->name(), s);
        }
    }
    return strParams;
}

VStringList V3HierBlock::commandArgs(bool forMkJson) const {
    VStringList opts;
    const string prefix = hierPrefix();
    if (!forMkJson) {
        opts.push_back(" --prefix " + prefix);
        opts.push_back(" --mod-prefix " + prefix);
        // Similar to --top-module but need to use encoded name(), not prettyName()
        opts.push_back(" --top-module-encoded " + modp()->name());
    }
    opts.push_back(" --lib-create " + modp()->name());  // possibly mangled name
    if (v3Global.opt.protectKeyProvided())
        opts.push_back(" --protect-key " + v3Global.opt.protectKeyDefaulted());
    opts.push_back(" --hierarchical-child " + cvtToStr(v3Global.opt.threads()));

    const StrGParams gparamsStr = stringifyParams(m_params, true);
    for (const StrGParam& param : gparamsStr) {
        opts.push_back("-G" + param.first + "=" + param.second + "");
    }
    if (!m_typeParams.empty()) {
        opts.push_back(" --hierarchical-params-file " + typeParametersFilename());
    }
    // Promoted references travel in a configuration file, not on the command
    // line: a large design can have far too many for the argument list.
    if (!m_xmrPorts.empty()) opts.push_back(" " + V3HierGraph::xmrPortsFilename());

    const int blockThreads = V3Control::getHierWorkers(m_modp->origName());
    if (blockThreads > 1) {
        if (!inEmpty()) {
            V3Control::getHierWorkersFileLine(m_modp->origName())
                ->v3warn(E_UNSUPPORTED, "Specifying workers for nested hierarchical blocks");
        } else {
            if (v3Global.opt.threads() < blockThreads) {
                m_modp->v3error("Hierarchical blocks cannot be scheduled on more threads than in "
                                "thread pool, threads = "
                                << v3Global.opt.threads()
                                << " hierarchical block threads = " << blockThreads);
            }

            opts.push_back(" --threads " + std::to_string(blockThreads));
        }
    }

    return opts;
}

VStringList V3HierBlock::hierBlockArgs() const {
    VStringList opts;
    const StrGParams gparamsStr = stringifyParams(m_params, false);
    opts.emplace_back("--hierarchical-block ");
    string s = modp()->origName();  // origName
    s += "," + modp()->name();  // mangledName
    for (const StrGParam& pair : gparamsStr) {
        s += "," + pair.first;
        s += "," + pair.second;
    }
    opts.back() += s;
    return opts;
}

string V3HierBlock::hierPrefix() const { return "V" + modp()->name(); }

string V3HierBlock::hierSomeFilename(bool withDir, const char* prefix, const char* suffix) const {
    string s;
    if (withDir) s = hierPrefix() + '/';
    s += prefix + modp()->name() + suffix;
    return s;
}

string V3HierBlock::hierWrapperFilename(bool withDir) const {
    return hierSomeFilename(withDir, "", ".sv");
}

string V3HierBlock::hierMkFilename(bool withDir) const {
    return hierSomeFilename(withDir, "V", ".mk");
}

string V3HierBlock::hierLibFilename(bool withDir) const {
    return hierSomeFilename(withDir, "lib", ".a");
}

string V3HierBlock::hierGeneratedFilenames(bool withDir) const {
    return hierWrapperFilename(withDir) + ' ' + hierMkFilename(withDir);
}

string V3HierBlock::vFileIfNecessary() const {
    string filename = V3Os::filenameRealPath(m_modp->fileline()->filename());
    for (const auto& v : v3Global.opt.vFiles()) {
        // Already listed in vFiles, so no need to add the file.
        if (filename == V3Os::filenameRealPath(v.filename())) return "";
    }
    return filename;
}

void V3HierBlock::writeCommandArgsFile(bool forMkJson) const {
    const std::unique_ptr<std::ofstream> of{V3File::new_ofstream(commandArgsFilename(forMkJson))};
    *of << "--cc\n";

    if (!forMkJson) {
        for (const V3GraphEdge& edge : outEdges()) {
            const V3HierBlock* const dependencyp = edge.top()->as<V3HierBlock>();
            *of << v3Global.opt.makeDir() << "/" << dependencyp->hierWrapperFilename(true) << "\n";
        }
        *of << "-Mdir " << v3Global.opt.makeDir() << "/" << hierPrefix() << " \n";
    }
    V3HierWriteCommonInputs(this, of.get(), forMkJson);
    const VStringList& commandOpts = commandArgs(false);
    for (const string& opt : commandOpts) *of << opt << "\n";
    *of << hierBlockArgs().front() << "\n";
    for (const V3GraphEdge& edge : outEdges()) {
        const V3HierBlock* const dependencyp = edge.top()->as<V3HierBlock>();
        *of << dependencyp->hierBlockArgs().front() << "\n";
    }
    *of << v3Global.opt.allArgsStringForHierBlock(false) << "\n";
}

string V3HierBlock::commandArgsFilename(bool forMkJson) const {
    return V3HierCommandArgsFilename(hierPrefix(), forMkJson);
}

string V3HierBlock::typeParametersFilename() const {
    return V3HierParametersFileName(hierPrefix());
}

void V3HierBlock::writeParametersFile() const {
    if (m_typeParams.empty()) return;

    VHashSha512 hash{"type params"};
    const string moduleName = "Vhsh" + hash.digestSymbol24();
    const std::unique_ptr<std::ofstream> of{V3File::new_ofstream(typeParametersFilename())};
    *of << "module " << moduleName << ";\n";
    for (AstParamTypeDType* const gparam : m_typeParams) {
        AstTypedef* tdefp
            = new AstTypedef{new FileLine{FileLine::builtInFilename()}, gparam->name(), nullptr,
                             VFlagChildDType{}, gparam->skipRefp()->cloneTreePure(true)};
        V3EmitV::verilogForTree(tdefp, *of);
        VL_DO_DANGLING(tdefp->deleteTree(), tdefp);
    }
    *of << "endmodule\n\n";
    *of << "`verilator_config\n";
    *of << "hier_params -module \"" << moduleName << "\"\n";
}

//######################################################################
// Construct graph of hierarchical blocks
class HierBlockUsageCollectVisitor final : public VNVisitorConst {
    // NODE STATE
    // AstNode::user1()            -> bool. Already visited
    const VNUser1InUse m_inuser1;

    // STATE
    V3HierGraph* const m_graphp = new V3HierGraph{};  // The graph of hierarchical blocks
    // Map from hier blocks to the corresponding V3HierBlock graph vertex
    std::unordered_map<const AstModule*, V3HierBlock*> m_mod2vtx;
    AstModule* m_modp = nullptr;  // The current module
    std::vector<AstVar*> m_params;  // Overridden value parameters of current module
    std::vector<AstParamTypeDType*> m_typeParams;  // Type parameters of current module
    // Hierarchical blocks instanciated (possibly indirectly) by current hierarchical block
    std::vector<V3HierBlock*> m_childrenp;

    // VISITORSs
    void visit(AstNodeModule*) override {}  // Ignore all non-AstModule
    void visit(AstModule* nodep) override {
        // Visit each module once
        if (nodep->user1SetOnce()) return;

        UINFO(5, "Visiting " << nodep->prettyNameQ());
        VL_RESTORER(m_modp);
        m_modp = nodep;

        // If not a hierarchical block, just iterate and return
        if (!nodep->hierBlock()) {
            iterateChildrenConst(nodep);
            return;
        }

        // This is a hierarchical block, gather parts
        VL_RESTORER_CLEAR(m_params);
        VL_RESTORER_CLEAR(m_typeParams);
        VL_RESTORER_CLEAR(m_childrenp);
        iterateChildrenConst(nodep);
        // Create the graph vertex for this hier block
        V3HierBlock* const blockp = new V3HierBlock{m_graphp, nodep, m_params, m_typeParams};
        // Record it
        m_mod2vtx[nodep] = blockp;
        // Add an edge to each child block
        for (V3HierBlock* const childp : m_childrenp) new V3GraphEdge{m_graphp, blockp, childp, 1};
    }
    void visit(AstCell* nodep) override {
        // Nothing to do for non-AstModules because hierarchical block cannot exist under them.
        AstModule* const modp = VN_CAST(nodep->modp(), Module);
        if (!modp) return;
        // Depth-first traversal of module hierechy
        iterateConst(modp);
        // If this is an instance of a hierarchical block, add to child array to link parent
        if (modp->hierBlock()) m_childrenp.emplace_back(m_mod2vtx.at(modp));
    }
    void visit(AstVar* nodep) override {
        if (!m_modp) return;
        if (!m_modp->hierBlock()) return;
        // Can't handle interface port on hier block
        if (nodep->isIfaceRef() && !nodep->isIfaceParent()) {
            nodep->v3error("Modport cannot be used at the hierarchical block boundary");
        }
        // Record overridden value parameter of this hier block
        if (nodep->isGParam() && nodep->overriddenParam()) {
            UASSERT_OBJ(m_modp, nodep, "Value parameter not under module");
            m_params.push_back(nodep);
        }
    }
    void visit(AstParamTypeDType* nodep) override {
        UASSERT_OBJ(m_modp, nodep, "Type parameter not under module");
        if (!m_modp->hierBlock()) return;
        // Record type parameter of this hier block
        m_typeParams.push_back(nodep);
    }

    void visit(AstNodeStmt*) override {}  // Accelerate
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstTypeTable*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTOR
    explicit HierBlockUsageCollectVisitor(AstNetlist* netlistp) {
        iterateChildrenConst(netlistp);
        if (dumpGraphLevel() >= 3) m_graphp->dumpDotFilePrefixed("hierblocks_initial");
        // Simplify dependencies
        m_graphp->removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
        // Topologically sorder the graph
        m_graphp->order();  // This is a bit heavy weight, but does produce a topological ordering
        if (dumpGraphLevel() >= 3) m_graphp->dumpDotFilePrefixed("hierblocks");
    }

public:
    static V3HierGraph* apply(AstNetlist* netlistp) {
        return HierBlockUsageCollectVisitor{netlistp}.m_graphp;
    }
};

VStringList V3HierGraph::sourceFiles(const string& topModuleFile) {
    VStringList sources;
    sources.reserve(v3Global.opt.vFiles().size() + 1);
    for (const VFileLibName& vfile : v3Global.opt.vFiles()) sources.emplace_back(vfile.filename());
    // Library-discovered blocks may depend on packages in the explicit input files.
    if (!topModuleFile.empty()) sources.emplace_back(topModuleFile);
    return sources;
}

string V3HierGraph::xmrPortsFilename() {
    return v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__hierXmrPorts.vlt";
}

// Describe every promoted reference in one configuration file, read by both the
// child runs (which create the ports) and the top run (which connects them).
void V3HierGraph::writeXmrPortsFile() const {
    bool any = false;
    for (const V3GraphVertex& vtx : vertices()) {
        if (!vtx.as<V3HierBlock>()->xmrPorts().empty()) any = true;
    }
    if (!any) return;
    const std::unique_ptr<std::ofstream> of{V3File::new_ofstream(xmrPortsFilename())};
    *of << "`verilator_config\n";
    for (const V3GraphVertex& vtx : vertices()) {
        const V3HierBlock* const blockp = vtx.as<V3HierBlock>();
        for (const V3HierBlock::XmrPort& port : blockp->xmrPorts()) {
            *of << "hier_xmr_port -module \"" << port.m_refModule << "\" -block \""
                << blockp->modp()->name() << "\" -port \"" << port.m_name << "\" -width "
                << port.m_width << (port.m_signed ? " -signed" : "") << " -scope \"" << port.m_path
                << "\"\n";
        }
    }
}

void V3HierGraph::writeCommandArgsFiles(bool forMkJson) const {
    writeXmrPortsFile();

    for (const V3GraphVertex& vtx : vertices()) {
        vtx.as<V3HierBlock>()->writeCommandArgsFile(forMkJson);
    }
    // For the top module
    const std::unique_ptr<std::ofstream> of{
        V3File::new_ofstream(topCommandArgsFilename(forMkJson))};
    if (!forMkJson) {
        // Load wrappers first not to be overwritten by the original HDL
        for (const V3GraphVertex& vtx : vertices()) {
            *of << vtx.as<V3HierBlock>()->hierWrapperFilename(true) << "\n";
        }
    }
    V3HierWriteCommonInputs(nullptr, of.get(), forMkJson);
    if (!forMkJson) {
        const VStringSet& cppFiles = v3Global.opt.cppFiles();
        for (const string& i : cppFiles) *of << i << "\n";
        *of << "--top-module " << v3Global.rootp()->topModulep()->name() << "\n";
        *of << "--prefix " << v3Global.opt.prefix() << "\n";
        *of << "-Mdir " << v3Global.opt.makeDir() << "\n";
        *of << "--mod-prefix " << v3Global.opt.modPrefix() << "\n";
    }
    for (const V3GraphVertex& vtx : vertices()) {
        *of << vtx.as<V3HierBlock>()->hierBlockArgs().front() << "\n";
    }

    // The top run needs the same promoted-port descriptions, to connect them
    for (const V3GraphVertex& vtx : vertices()) {
        if (!vtx.as<V3HierBlock>()->xmrPorts().empty()) {
            *of << xmrPortsFilename() << "\n";
            break;
        }
    }

    if (!v3Global.opt.libCreate().empty()) {
        *of << "--lib-create " << v3Global.opt.libCreate() << "\n";
    }
    if (v3Global.opt.protectKeyProvided()) {
        *of << "--protect-key " << v3Global.opt.protectKeyDefaulted() << "\n";
    }
    *of << "--threads " << cvtToStr(v3Global.opt.threads()) << "\n";
    *of << (v3Global.opt.systemC() ? "--sc" : "--cc") << "\n";
    *of << v3Global.opt.allArgsStringForHierBlock(true) << "\n";
}

string V3HierGraph::topCommandArgsFilename(bool forMkJson) {
    return V3HierCommandArgsFilename(v3Global.opt.prefix(), forMkJson);
}

void V3HierGraph::writeParametersFiles() const {
    for (const V3GraphVertex& vtx : vertices()) { vtx.as<V3HierBlock>()->writeParametersFile(); }
}

//######################################################################

// Width of a signal that can be promoted to a port, or -1 if it cannot be.
// Runs before V3Width, so only a packed basic type with a literal range can be
// sized; everything else returns -1 and the caller refuses.
static int promotableWidth(const AstVar* varp, bool& isSignedr) {
    // Follow typedefs: a name for a packed basic type is still promotable
    const AstNodeDType* subp = varp->subDTypep();
    if (subp) subp = subp->skipRefp();
    const AstBasicDType* const bdtypep = VN_CAST(subp, BasicDType);
    if (!bdtypep) return -1;  // struct, enum, unpacked array, class, ...
    isSignedr = bdtypep->isSigned();
    // isOpaque() covers real, string, event and the internal types; a bare
    // 'input foo' is LOGIC_IMPLICIT, which isIntNumeric() would wrongly reject.
    if (bdtypep->keyword().isOpaque()) return -1;
    if (const AstRange* const rangep = bdtypep->rangep()) {
        const AstConst* const lp = VN_CAST(rangep->leftp(), Const);
        const AstConst* const rp = VN_CAST(rangep->rightp(), Const);
        if (!lp || !rp) return -1;  // parameterized: not resolvable yet
        const int l = lp->toSInt();
        const int r = rp->toSInt();
        return (l > r ? l - r : r - l) + 1;
    }
    if (bdtypep->isRanged()) return bdtypep->hi() - bdtypep->lo() + 1;
    return 1;  // plain scalar
}

// Everything scanning one block needs, so the per-reference work below is a
// named function rather than a lambda nested inside two loops.
struct XRefScan final {
    AstModule* const m_blockp;  // Block being scanned
    V3HierBlock* const m_blockVtxp;  // Its vertex in the plan
    const VInsertionSet<AstNodeModule*>& m_inBlock;  // Modules inside the block
    const std::unordered_map<const AstVar*, AstNodeModule*>& m_varToMod;  // Each variable's module
    const std::unordered_map<const AstNodeFTask*, AstNodeModule*>&
        m_taskToMod;  // Each task's module
    const std::map<std::string, AstNodeModule*>& m_declared;  // Names the block already declares
    const bool m_hasNestedBlock;  // An inner block is already a wrapper
    std::map<std::string, std::string> m_pathToPort{};  // One port per distinct path
    std::set<std::pair<std::string, std::string>> m_seen{};  // (module, path) already emitted
    size_t m_count = 0;  // References promoted
};

// Record one reference out of the block as a port to promote, or refuse it.
static void collectOutboundXRef(XRefScan& scan, AstNodeModule* modp, AstVarXRef* xrefp) {
    if (!xrefp->varp()) return;
    const auto vit = scan.m_varToMod.find(xrefp->varp());
    AstNodeModule* const targetp = vit == scan.m_varToMod.cend() ? nullptr : vit->second;
    // An interface port member is not an outbound reference: the
    // block reaches it through its own port, and interfaces at a
    // hierarchical block boundary are diagnosed separately (see the
    // modport check in HierBlockUsageCollectVisitor).
    if (VN_IS(targetp, Iface)) return;
    if (targetp && !scan.m_inBlock.exists(targetp)) {
        if (scan.m_hasNestedBlock) {
            xrefp->v3warn(E_UNSUPPORTED, "Cannot promote reference out of hierarchical block "
                                             << scan.m_blockp->prettyNameQ()
                                             << ": it contains a nested hierarchical block");
            return;
        }
        // Only reads can be promoted. A written reference would need
        // an output port and raises ordering questions this does not
        // address; refuse it rather than silently mis-modelling it.
        if (xrefp->access().isWriteOrRW()) {
            xrefp->v3warn(E_UNSUPPORTED, "Writing a signal outside a hierarchical block: '"
                                             << xrefp->dotted() << "." << xrefp->name() << "'");
            return;
        }
        // The rewrite in the child run matches a chain of plain names, so an
        // indexed scope cannot be spelled back; by here the index has already
        // become __BRA__n__KET__. Detection would otherwise promote it and the
        // child run would not find the name at all.
        if (xrefp->dotted().find("__BRA__") != std::string::npos
            || xrefp->dotted().find('[') != std::string::npos) {
            xrefp->v3warn(E_UNSUPPORTED, "Cannot promote reference out of a hierarchical block: '"
                                             << AstNode::prettyName(xrefp->dotted()) << "."
                                             << xrefp->name() << "' indexes a scope");
            return;
        }
        // A parameter is a constant, and a port is not: promoting one would
        // leave constant contexts like 'ph[P]' or '[P-1:0]' reading a runtime
        // value. The child run resolves its own parameters, so refuse instead.
        if (xrefp->varp()->isParam()) {
            xrefp->v3warn(E_UNSUPPORTED, "Cannot promote reference out of a hierarchical block: '"
                                             << xrefp->dotted() << "." << xrefp->name()
                                             << "' is a parameter, which a port cannot carry");
            return;
        }
        ++scan.m_count;
        const std::string path = xrefp->dotted() + "." + xrefp->name();
        // Index-based name: flattening the path to an identifier is
        // not injective ("a.b_c" and "a_b.c" collide), and the path
        // is passed explicitly anyway.
        V3HierBlock* const blockVtxp = scan.m_blockVtxp;
        // Modules sharing a path share its port; each module that
        // reads it still needs its own entry, because the rewrite
        // is matched per module.
        auto pit = scan.m_pathToPort.find(path);
        const bool newPort = pit == scan.m_pathToPort.cend();
        const std::string portName
            = newPort ? "xmrport_" + cvtToStr(scan.m_pathToPort.size()) : pit->second;
        // The synthesized name must not shadow anything the design
        // already declares anywhere in the block's subtree.
        const auto dit = scan.m_declared.find(portName);
        if (dit != scan.m_declared.cend()) {
            xrefp->v3warn(E_UNSUPPORTED, "Cannot promote reference out of a hierarchical block: "
                                         "generated port name '"
                                             << portName
                                             << "' collides with an existing signal in "
                                             << dit->second->prettyNameQ());
            return;
        }
        if (newPort) scan.m_pathToPort.emplace(path, portName);
        if (scan.m_seen.insert(std::make_pair(modp->name(), path)).second) {
            // V3Width has not run in this pass - createGraph returns
            // before it - so varp()->width() is 0 and dtypep() is null.
            // The width has to come from the scan.m_declared type, and any
            // type whose width cannot be established exactly here is
            // refused rather than guessed: a silently wrong width
            // would mean silently wrong hardware.
            bool isSigned = false;
            const int width = promotableWidth(xrefp->varp(), isSigned);
            if (width < 0) {
                xrefp->v3warn(E_UNSUPPORTED,
                              "Cannot promote reference out of a hierarchical block: '"
                                  << path
                                  << "' does not have a width known before "
                                     "elaboration (parameterized, unpacked, or "
                                     "non-integral type)");
                return;
            }
            // origName, not name: a de-parameterized module is
            // mangled differently between runs
            blockVtxp->addXmrPort(
                V3HierBlock::XmrPort{modp->name(), portName, path, width, isSigned});
            if (modp->origName() != modp->name()) {
                blockVtxp->addXmrPort(
                    V3HierBlock::XmrPort{modp->origName(), portName, path, width, isSigned});
            }
        }
        UINFO(4, "HIER-XMR: " << scan.m_blockp->prettyNameQ() << " -> '" << xrefp->dotted() << "."
                              << xrefp->name() << "' in " << targetp->prettyNameQ() << " => port "
                              << portName);
    }
}

// A dotted call out of the block cannot become a port: a port carries a value,
// not a task or function. Left alone it reaches the child run as a bare "Can't
// find definition" error, so name it here instead.
static void refuseOutboundFTaskRef(const XRefScan& scan, AstNodeFTaskRef* refp) {
    if (refp->dotted().empty() || !refp->taskp()) return;
    const auto it = scan.m_taskToMod.find(refp->taskp());
    if (it == scan.m_taskToMod.cend()) return;
    if (scan.m_inBlock.exists(it->second)) return;
    refp->v3warn(E_UNSUPPORTED, "Cannot promote reference out of a hierarchical block: '"
                                    << refp->dotted() << "." << refp->name()
                                    << "' is a function or task, which a port cannot carry");
}

static void detectOutboundXRefs(AstNetlist* netlistp, V3HierGraph* graphp) {
    // Which module each variable lives in, built in one pass; walking backp()
    // per reference would be quadratic
    std::unordered_map<const AstVar*, AstNodeModule*> varToMod;
    std::unordered_map<const AstNodeFTask*, AstNodeModule*> taskToMod;
    netlistp->foreach([&varToMod, &taskToMod](AstNodeModule* modp) {
        modp->foreach([&varToMod, modp](AstVar* varp) { varToMod.emplace(varp, modp); });
        modp->foreach([&taskToMod, modp](AstNodeFTask* taskp) { taskToMod.emplace(taskp, modp); });
    });
    // Vertex per block, so findings attach to the plan rather than to file statics
    std::map<const AstModule*, V3HierBlock*> mod2vtx;
    for (V3GraphVertex& vtx : graphp->vertices()) {
        V3HierBlock* const blockVtxp = vtx.as<V3HierBlock>();
        mod2vtx[blockVtxp->modp()] = blockVtxp;
    }
    netlistp->foreach([&mod2vtx, &varToMod, &taskToMod](AstModule* blockp) {
        if (!blockp->hierBlock()) return;
        // Every module in this block's subtree
        VInsertionSet<AstNodeModule*> inBlock;
        std::vector<AstNodeModule*> todo{blockp};
        while (!todo.empty()) {
            AstNodeModule* const modp = todo.back();
            todo.pop_back();
            if (!inBlock.insert(modp)) continue;
            modp->foreach([&todo](AstCell* cellp) {
                if (cellp->modp()) todo.push_back(cellp->modp());
            });
        }
        // A nested hierarchical block inside this one cannot be threaded
        // through: by the time this block is compiled, the inner block is
        // already a wrapper, so there is no reference left to rewrite and no
        // way to create the port. Refuse rather than emit a half-connected
        // model.
        bool hasNestedBlock = false;
        for (AstNodeModule* const modp : inBlock) {
            if (modp != blockp && modp->hierBlock()) hasNestedBlock = true;
        }

        // Names declared anywhere in the block, gathered once: checking each
        // generated name against every variable of every module would be
        // quadratic in the number of promoted references.
        std::map<std::string, AstNodeModule*> declared;
        for (AstNodeModule* const modp : inBlock) {
            modp->foreach(
                [&declared, modp](AstVar* varp) { declared.emplace(varp->name(), modp); });
        }
        XRefScan scan{blockp,    mod2vtx.at(blockp), inBlock,       varToMod,
                      taskToMod, declared,           hasNestedBlock};
        for (AstNodeModule* const modp : inBlock) {
            modp->foreach(
                [&scan, modp](AstVarXRef* xrefp) { collectOutboundXRef(scan, modp, xrefp); });
            modp->foreach([&scan](AstNodeFTaskRef* refp) { refuseOutboundFTaskRef(scan, refp); });
        }
        if (scan.m_count) {
            UINFO(4, "HIER-XMR: block " << blockp->prettyNameQ() << " has " << scan.m_count
                                        << " outbound XMR(s) needing promotion to ports");
        }
    });
}

void V3Hierarchical::createGraph(AstNetlist* netlistp) {
    UASSERT(!v3Global.hierGraphp(), "Should only be called once");

    AstNodeModule* const modp = netlistp->topModulep();
    if (modp->hierBlock()) {
        modp->v3warn(HIERBLOCK, "Top module marked as hierarchical block, ignoring\n"
                                    + modp->warnMore()
                                    + "... Suggest remove verilator hier_block on this module");
        modp->hierBlock(false);
    }

    V3HierGraph* const graphp = HierBlockUsageCollectVisitor::apply(netlistp);
    detectOutboundXRefs(netlistp, graphp);
    V3Stats::addStat("HierBlock, Hierarchical blocks", graphp->vertices().size());
    // No hierarchical block is found, nothing to do.
    if (graphp->empty()) {
        VL_DO_DANGLING(delete graphp, graphp);
        return;
    }
    // Hold on to the graph
    v3Global.hierGraphp(graphp);
}

//######################################################################
// Promote outbound XMRs to ports in the child run

// Flatten a DOT chain of PARSEREFs into "a.b.c". A trailing bit or part select
// is permitted and reported through selp: "a.b.c[2]" parses as the select
// hanging off the last identifier, inside the chain, and the select must be
// kept and re-applied to the promoted port.
static bool flattenDot(AstNode* nodep, std::vector<std::string>& names,
                       AstNodePreSel** selpp = nullptr) {
    if (AstDot* const dotp = VN_CAST(nodep, Dot)) {
        return flattenDot(dotp->lhsp(), names, selpp) && flattenDot(dotp->rhsp(), names, selpp);
    }
    if (AstNodePreSel* const selp = VN_CAST(nodep, NodePreSel)) {
        // Only a select directly on the final identifier can be handled
        if (!selpp || *selpp) return false;
        AstParseRef* const refp = VN_CAST(selp->fromp(), ParseRef);
        if (!refp || refp->lhsp() || refp->ftaskrefp()) return false;
        names.push_back(refp->name());
        *selpp = selp;
        return true;
    }
    if (AstParseRef* const refp = VN_CAST(nodep, ParseRef)) {
        if (refp->lhsp() || refp->ftaskrefp()) return false;
        names.push_back(refp->name());
        return true;
    }
    return false;
}

// Width and signedness of a port to create
struct PortSpec final {
    int m_width;  // Declared width
    bool m_signed;  // Declared signed
};

// What a module already has, so neither the names nor the pin numbering needs
// a scan of the module on each added port.
struct PortState final {
    std::set<std::string> m_names{};  // Ports present
    int m_maxPin = -1;  // Highest pin number in use, -1 until counted
};

// Add an input port to modp, if not already present. Returns the variable.
static AstVar* ensurePort(AstNodeModule* modp, const std::string& name, const PortSpec& spec,
                          AstNetlist* netlistp, std::map<AstNodeModule*, PortState>& havePort) {
    PortState& state = havePort[modp];
    // Membership is tracked as ports are added; a foreach over every variable
    // on each call would be quadratic
    if (!state.m_names.insert(name).second) return nullptr;
    const VSigning numeric = spec.m_signed ? VSigning::SIGNED : VSigning::UNSIGNED;
    AstNodeDType* const dtypep = (spec.m_width <= 1 && !spec.m_signed)
                                     ? netlistp->findBitDType()
                                     : netlistp->findBitDType(spec.m_width, spec.m_width, numeric);
    AstVar* const varp = new AstVar{modp->fileline(), VVarType::PORT, name, dtypep};
    varp->direction(VDirection::INPUT);
    varp->declDirection(VDirection::INPUT);
    // An IO variable must also appear in the module's port list, which is a
    // separate AstPort list; a bare AstVar is rejected as not in the port list.
    if (state.m_maxPin < 0) {  // Count the existing ports once per module
        state.m_maxPin = 0;
        modp->foreach([&state](AstPort* portp) {
            state.m_maxPin = std::max(state.m_maxPin, portp->pinNum());
        });
    }
    modp->addStmtsp(new AstPort{modp->fileline(), ++state.m_maxPin, name});
    modp->addStmtsp(varp);
    UINFO(4, "HIER-XMR: added port " << name << " to " << modp->prettyNameQ());
    return varp;
}

// Give one instance the ports its module needs, and its parent the same ports
// to drive them with. Returns true if anything was added.
static bool threadCellPorts(AstCell* cellp,
                            std::map<AstNodeModule*, std::map<std::string, PortSpec>>& needs,
                            AstNetlist* netlistp, std::map<AstNodeModule*, PortState>& havePort) {
    AstNodeModule* const childp = cellp->modp();
    if (!childp) return false;
    const auto it = needs.find(childp);
    if (it == needs.end()) return false;
    AstNodeModule* parentp = nullptr;
    for (AstNode* upp = cellp; upp; upp = upp->backp()) {
        if ((parentp = VN_CAST(upp, NodeModule))) break;
    }
    if (!parentp) return false;
    bool changed = false;
    for (const auto& np : it->second) {
        const std::string& name = np.first;
        bool havePin = false;
        for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->name() == name) havePin = true;
        }
        if (havePin) continue;
        ensurePort(parentp, name, np.second, netlistp, havePort);
        needs[parentp].emplace(name, np.second);
        cellp->addPinsp(
            new AstPin{cellp->fileline(), -1, name, new AstParseRef{cellp->fileline(), name}});
        UINFO(4, "HIER-XMR: pinned " << name << " on instance " << cellp->prettyNameQ());
        changed = true;
    }
    return changed;
}

void V3Hierarchical::promoteXmrPorts(AstNetlist* netlistp) {
    // This run's top module is the hierarchical block being compiled
    const std::vector<V3Control::HierXmrPort>* const wantedp
        = V3Control::getHierXmrPorts(v3Global.opt.topModule());
    if (!wantedp) return;
    // (module the reference is in, dotted path) -> the port it becomes. A dotted
    // path is relative to its module, so matching on the text alone would rewrite
    // an unrelated module's identically-spelled internal reference.
    struct Want final {
        std::string m_port;  // Port the reference becomes
        int m_width;  // Width to declare it
        bool m_signed;  // Whether to declare it signed
    };
    std::map<std::pair<std::string, std::string>, Want> wanted;
    for (const V3Control::HierXmrPort& port : *wantedp) {
        wanted.emplace(std::make_pair(port.m_refModule, port.m_path),
                       Want{port.m_port, port.m_width, port.m_signed});
    }

    // 1) Rewrite each matching hierarchical name into a read of a new port.
    //    Collect first: replaceWith/deleteTree on the node being traversed
    //    corrupts the iteration.
    // module -> (port name, width) it must declare
    std::map<AstNodeModule*, std::map<std::string, PortSpec>> needs;
    struct Hit final {
        AstDot* m_dotp;  // The reference to rewrite
        AstNodeModule* m_modp;  // Module the reference is in
        std::string m_portName;  // Port it becomes
    };
    std::vector<Hit> hits;
    netlistp->foreach([&](AstDot* dotp) {
        if (VN_IS(dotp->backp(), Dot)) return;  // only the outermost of a chain
        std::vector<std::string> names;
        AstNodePreSel* selp = nullptr;
        if (!flattenDot(dotp, names, &selp) || names.size() < 2) return;
        std::string path;
        for (size_t i = 0; i < names.size(); ++i) {
            if (i) path += '.';
            path += names[i];
        }
        AstNodeModule* modp = nullptr;
        for (AstNode* upp = dotp; upp; upp = upp->backp()) {
            if ((modp = VN_CAST(upp, NodeModule))) break;
        }
        if (!modp) return;
        // The module may be de-parameterized differently between runs, so accept
        // either spelling; both are still scoped to this module, which is what
        // stops an unrelated module's identical path from matching.
        auto wit = wanted.find(std::make_pair(modp->name(), path));
        if (wit == wanted.end()) wit = wanted.find(std::make_pair(modp->origName(), path));
        if (wit == wanted.end()) return;
        needs[modp].emplace(wit->second.m_port,
                            PortSpec{wit->second.m_width, wit->second.m_signed});
        hits.push_back(Hit{dotp, modp, wit->second.m_port});
    });

    // Detection works from resolved references and the rewrite above from plain
    // name chains, so a path form only one of them accepts would reach the rest
    // of the run as a bare "Can't find definition". A de-parameterized module
    // contributes two spellings of the same port, so a port is satisfied when
    // any of its entries matched.
    std::set<std::string> rewritten;
    for (const Hit& hit : hits) rewritten.insert(hit.m_portName);
    for (const V3Control::HierXmrPort& port : *wantedp) {
        if (!rewritten.count(port.m_port)) {  // LCOV_EXCL_START
            netlistp->v3fatalSrc("Promoted reference '"
                                 << port.m_path << "' in " << port.m_refModule
                                 << " was not rewritten to port '" << port.m_port << "'");
        }  // LCOV_EXCL_STOP
    }

    for (const Hit& hit : hits) {
        AstDot* const dotp = hit.m_dotp;
        // Re-find the select; the earlier walk was only to match the path
        std::vector<std::string> names;
        AstNodePreSel* selp = nullptr;
        flattenDot(dotp, names, &selp);
        AstNodeExpr* newp = new AstParseRef{dotp->fileline(), hit.m_portName};
        if (selp) {
            // Keep the select, re-based on the promoted port
            AstNodePreSel* const keepSelp = selp->unlinkFrBack();
            keepSelp->fromp()->unlinkFrBack()->deleteTree();
            keepSelp->fromp(newp);
            newp = keepSelp;
        }
        dotp->replaceWith(newp);
        VL_DO_DANGLING(dotp->deleteTree(), dotp);
        UINFO(4, "HIER-XMR: rewrote reference to " << hit.m_portName << " in "
                                                   << hit.m_modp->prettyNameQ());
    }
    if (needs.empty()) return;

    // 2) Create the ports where the references were
    std::map<AstNodeModule*, PortState> havePort;
    for (const auto& pair : needs) {
        for (const auto& np : pair.second) {
            ensurePort(pair.first, np.first, np.second, netlistp, havePort);
        }
    }

    // 3) Thread each port up to the block top, adding a pin at every instance.
    //    Adding a port to a parent may require its own parent to supply it, so
    //    the deepest module is taken first and one pass then suffices, where
    //    repeating to a fixpoint would cost depth x cells. modulesp() is sorted
    //    root first (V3LinkLevel::modSortByLevel), so reversing gives that
    //    order. The cells are gathered first, because creating ports and pins
    //    mutates the tree a traversal would be walking.
    std::vector<AstCell*> cells;
    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        modp->foreach([&cells](AstCell* cellp) { cells.push_back(cellp); });
    }
    std::reverse(cells.begin(), cells.end());
    for (AstCell* const cellp : cells) threadCellPorts(cellp, needs, netlistp, havePort);
}

// In the top run, connect each promoted port to the signal it came from. The
// full hierarchy is present here, so the rebuilt dotted reference resolves.
void V3Hierarchical::bindXmrPorts(AstNetlist* netlistp) {
    // Collect first: adding pins during the traversal mutates the tree being
    // walked, and the additions do not survive.
    std::vector<AstCell*> targets;
    netlistp->foreach([&targets](AstCell* cellp) {
        if (V3Control::getHierXmrPorts(cellp->modName())) targets.push_back(cellp);
    });
    for (AstCell* const cellp : targets) {
        // Index the pins once; scanning per port would be quadratic
        std::map<std::string, AstPin*> pinByName;
        for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinByName.emplace(pinp->name(), pinp);
        }
        for (const V3Control::HierXmrPort& pr : *V3Control::getHierXmrPorts(cellp->modName())) {
            // Linking already created a pin for every port of the instantiated
            // module, with a null expression for the ones the source does not
            // connect - which is exactly what PINMISSING reports. So fill that
            // pin in rather than adding another.
            const auto pit = pinByName.find(pr.m_port);
            AstPin* const existingp = pit == pinByName.cend() ? nullptr : pit->second;
            if (existingp && existingp->exprp()) continue;  // already connected
            AstNodeExpr* exprp = nullptr;
            std::string rest = pr.m_path;
            while (!rest.empty()) {
                const size_t dot = rest.find('.');
                const std::string part = (dot == std::string::npos) ? rest : rest.substr(0, dot);
                rest = (dot == std::string::npos) ? "" : rest.substr(dot + 1);
                AstParseRef* const refp = new AstParseRef{cellp->fileline(), part};
                exprp = exprp ? static_cast<AstNodeExpr*>(
                                    new AstDot{cellp->fileline(), false, exprp, refp})
                              : static_cast<AstNodeExpr*>(refp);
            }
            // V3LinkCells has already created a pin for every port of the
            // instantiated module, so there is always one to fill here.
            UASSERT_OBJ(existingp, cellp, "No pin for promoted port " + pr.m_port);
            existingp->exprp(exprp);
            UINFO(4, "HIER-XMR: bound " << pr.m_port << " to " << pr.m_path << " on "
                                        << cellp->prettyNameQ());
        }
    }
}
