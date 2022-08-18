// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// NO EDITS: Don't replace or delete nodes, as the parser symbol table
//           has pointers into the ast tree.
//
// LINK TRANSFORMATIONS:
//      Top-down traversal
//          Cells:
//              Read module if needed
//              Link to module that instantiates it
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3LinkCells.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Parse.h"
#include "V3SymTable.h"

#include <algorithm>
#include <map>
#include <unordered_set>
#include <vector>

//######################################################################
// Graph subclasses

class LinkCellsGraph final : public V3Graph {
public:
    LinkCellsGraph() = default;
    virtual ~LinkCellsGraph() override = default;
    virtual void loopsMessageCb(V3GraphVertex* vertexp) override;
};

class LinkCellsVertex final : public V3GraphVertex {
    AstNodeModule* const m_modp;

public:
    LinkCellsVertex(V3Graph* graphp, AstNodeModule* modp)
        : V3GraphVertex{graphp}
        , m_modp{modp} {}
    virtual ~LinkCellsVertex() override = default;
    AstNodeModule* modp() const { return m_modp; }
    virtual string name() const override { return modp()->name(); }
    virtual FileLine* fileline() const override { return modp()->fileline(); }
    // Recursive modules get space for maximum recursion
    virtual uint32_t rankAdder() const override {
        return m_modp->recursiveClone() ? (1 + v3Global.opt.moduleRecursionDepth()) : 1;
    }
};

class LibraryVertex final : public V3GraphVertex {
public:
    explicit LibraryVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    virtual ~LibraryVertex() override = default;
    virtual string name() const override { return "*LIBRARY*"; }
};

void LinkCellsGraph::loopsMessageCb(V3GraphVertex* vertexp) {
    if (const LinkCellsVertex* const vvertexp = dynamic_cast<LinkCellsVertex*>(vertexp)) {
        vvertexp->modp()->v3warn(E_UNSUPPORTED,
                                 "Unsupported: Recursive multiple modules (module instantiates "
                                 "something leading back to itself): "
                                     << vvertexp->modp()->prettyNameQ() << '\n'
                                     << V3Error::warnMore()
                                     << "... note: self-recursion (module instantiating itself "
                                        "directly) is supported.");
        V3Error::abortIfErrors();
    } else {  // Everything should match above, but...
        v3fatalSrc("Recursive instantiations");
    }
}

//######################################################################
// Link state, as a visitor of each AstNode

class LinkCellsVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstNodeModule::user1p()        // V3GraphVertex*    Vertex describing this module
    //   AstNodeModule::user2p()        // AstNodeModule*    clone used for de-recursing
    //   AstCell::user1p()              // ==V3NodeModule* if done, != if unprocessed
    //   AstCell::user2()               // bool   clone renaming completed
    //  Allocated across all readFiles in V3Global::readFiles:
    //   AstNode::user4p()      // VSymEnt*    Package and typedef symbol names
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    VInFilter* const m_filterp;  // Parser filter
    V3ParseSym* m_parseSymp;  // Parser symbol table

    // Below state needs to be preserved between each module call.
    AstNodeModule* m_modp = nullptr;  // Current module
    VSymGraph m_mods;  // Symbol table of all module names
    LinkCellsGraph m_graph;  // Linked graph of all cell interconnects
    LibraryVertex* m_libVertexp = nullptr;  // Vertex at root of all libraries
    const V3GraphVertex* m_topVertexp = nullptr;  // Vertex of top module
    std::unordered_set<string> m_declfnWarned;  // Files we issued DECLFILENAME on
    string m_origTopModuleName;  // original name of the top module

    VL_DEBUG_FUNC;  // Declare debug()

    // METHODS
    V3GraphVertex* vertex(AstNodeModule* nodep) {
        // Return corresponding vertex for this module
        if (!nodep->user1p()) nodep->user1p(new LinkCellsVertex(&m_graph, nodep));
        return nodep->user1u().toGraphVertex();
    }

    AstNodeModule* findModuleSym(const string& modName) {
        const VSymEnt* const foundp = m_mods.rootp()->findIdFallback(modName);
        if (!foundp) {
            return nullptr;
        } else {
            return VN_AS(foundp->nodep(), NodeModule);
        }
    }

    AstNodeModule* resolveModule(AstNode* nodep, const string& modName) {
        AstNodeModule* modp = findModuleSym(modName);
        if (!modp) {
            // Read-subfile
            // If file not found, make AstNotFoundModule, rather than error out.
            // We'll throw the error when we know the module will really be needed.
            const string prettyName = AstNode::prettyName(modName);
            V3Parse parser(v3Global.rootp(), m_filterp, m_parseSymp);
            // true below -> other simulators treat modules in link-found files as library cells
            parser.parseFile(nodep->fileline(), prettyName, true, "");
            V3Error::abortIfErrors();
            // We've read new modules, grab new pointers to their names
            readModNames();
            // Check again
            modp = findModuleSym(modName);
            if (!modp) {
                // This shouldn't throw a message as parseFile will create
                // a AstNotFoundModule for us
                nodep->v3error("Can't resolve module reference: '" << prettyName << "'");
            }
        }
        return modp;
    }

    // VISITs
    virtual void visit(AstNetlist* nodep) override {
        AstNode::user1ClearTree();
        readModNames();
        iterateChildren(nodep);
        // Find levels in graph
        m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
        m_graph.dumpDotFilePrefixed("linkcells");
        m_graph.rank();
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (const LinkCellsVertex* const vvertexp = dynamic_cast<LinkCellsVertex*>(itp)) {
                // +1 so we leave level 1  for the new wrapper we'll make in a moment
                AstNodeModule* const modp = vvertexp->modp();
                modp->level(vvertexp->rank() + 1);
            }
        }
        if (v3Global.opt.topModule() != "" && !m_topVertexp) {
            v3error("Specified --top-module '" << v3Global.opt.topModule()
                                               << "' was not found in design.");
        }
    }
    virtual void visit(AstConstPool* nodep) override {}
    virtual void visit(AstNodeModule* nodep) override {
        // Module: Pick up modnames, so we can resolve cells later
        VL_RESTORER(m_modp);
        {
            // For nested modules/classes, child below parent
            if (m_modp) new V3GraphEdge{&m_graph, vertex(m_modp), vertex(nodep), 1};
            //
            m_modp = nodep;
            UINFO(4, "Link Module: " << nodep << endl);
            if (nodep->fileline()->filebasenameNoExt() != nodep->prettyName()
                && !v3Global.opt.isLibraryFile(nodep->fileline()->filename())
                && !VN_IS(nodep, NotFoundModule) && !nodep->recursiveClone()
                && !nodep->internal()) {
                // We only complain once per file, otherwise library-like files
                // have a huge mess of warnings
                if (m_declfnWarned.find(nodep->fileline()->filename()) == m_declfnWarned.end()) {
                    m_declfnWarned.insert(nodep->fileline()->filename());
                    nodep->v3warn(DECLFILENAME, "Filename '"
                                                    << nodep->fileline()->filebasenameNoExt()
                                                    << "' does not match " << nodep->typeName()
                                                    << " name: " << nodep->prettyNameQ());
                }
            }
            if (VN_IS(nodep, Iface) || VN_IS(nodep, Package)) {
                nodep->inLibrary(true);  // Interfaces can't be at top, unless asked
            }
            const bool topMatch = (v3Global.opt.topModule() == nodep->prettyName());
            if (topMatch) {
                m_topVertexp = vertex(nodep);
                UINFO(2, "Link --top-module: " << nodep << endl);
                nodep->inLibrary(false);  // Safer to make sure it doesn't disappear
            }
            if (v3Global.opt.topModule() == "" ? nodep->inLibrary()  // Library cells are lower
                                               : !topMatch) {  // Any non-specified module is lower
                // Put under a fake vertex so that the graph ranking won't indicate
                // this is a top level module
                if (!m_libVertexp) m_libVertexp = new LibraryVertex(&m_graph);
                new V3GraphEdge(&m_graph, m_libVertexp, vertex(nodep), 1, false);
            }
            // Note AstBind also has iteration on cells
            iterateChildren(nodep);
            nodep->checkTree();
        }
    }

    virtual void visit(AstIfaceRefDType* nodep) override {
        // Cell: Resolve its filename.  If necessary, parse it.
        UINFO(4, "Link IfaceRef: " << nodep << endl);
        // Use findIdUpward instead of findIdFlat; it doesn't matter for now
        // but we might support modules-under-modules someday.
        AstNodeModule* const modp = resolveModule(nodep, nodep->ifaceName());
        if (modp) {
            if (VN_IS(modp, Iface)) {
                // Track module depths, so can sort list from parent down to children
                new V3GraphEdge(&m_graph, vertex(m_modp), vertex(modp), 1, false);
                if (!nodep->cellp()) nodep->ifacep(VN_AS(modp, Iface));
            } else if (VN_IS(modp, NotFoundModule)) {  // Will error out later
            } else {
                nodep->v3error("Non-interface used as an interface: " << nodep->prettyNameQ());
            }
        }
        // Note cannot do modport resolution here; modports are allowed underneath generates
    }

    virtual void visit(AstPackageImport* nodep) override {
        // Package Import: We need to do the package before the use of a package
        iterateChildren(nodep);
        UASSERT_OBJ(nodep->packagep(), nodep, "Unlinked package");  // Parser should set packagep
        new V3GraphEdge(&m_graph, vertex(m_modp), vertex(nodep->packagep()), 1, false);
    }

    virtual void visit(AstBind* nodep) override {
        // Bind: Has cells underneath that need to be put into the new
        // module, and cells which need resolution
        // TODO this doesn't allow bind to dotted hier names, that would require
        // this move to post param, which would mean we do not auto-read modules
        // and means we cannot compute module levels until later.
        UINFO(4, "Link Bind: " << nodep << endl);
        AstNodeModule* const modp = resolveModule(nodep, nodep->name());
        if (modp) {
            AstNode* const cellsp = nodep->cellsp()->unlinkFrBackWithNext();
            // Module may have already linked, so need to pick up these new cells
            VL_RESTORER(m_modp);
            {
                m_modp = modp;
                // Important that this adds to end, as next iterate assumes does all cells
                modp->addStmtp(cellsp);
                iterateAndNextNull(cellsp);
            }
        }
        pushDeletep(nodep->unlinkFrBack());
    }

    virtual void visit(AstCell* nodep) override {
        // Cell: Resolve its filename.  If necessary, parse it.
        // Execute only once.  Complication is that cloning may result in
        // user1 being set (for pre-clone) so check if user1() matches the
        // m_mod, if 0 never did it, if !=, it is an unprocessed clone
        const bool cloned = (nodep->user1p() && nodep->user1p() != m_modp);
        if (nodep->user1p() == m_modp) return;  // AstBind and AstNodeModule may call a cell twice
        if (nodep->modName() == m_origTopModuleName) {
            if (v3Global.opt.hierChild() && nodep->modName() == m_modp->origName()) {
                // Only the root of the recursive instantiation can be a hierarchical block.
                nodep->modName(m_modp->name());
            } else {
                // non-top module will be the top module of this run
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
        }
        nodep->user1p(m_modp);
        //
        if (!nodep->modp() || cloned) {
            UINFO(4, "Link Cell: " << nodep << endl);
            // Use findIdFallback instead of findIdFlat; it doesn't matter for now
            // but we might support modules-under-modules someday.
            AstNodeModule* cellmodp = resolveModule(nodep, nodep->modName());
            if (cellmodp) {
                if (cellmodp == m_modp || cellmodp->user2p() == m_modp) {
                    UINFO(1, "Self-recursive module " << cellmodp << endl);
                    cellmodp->recursive(true);
                    nodep->recursive(true);
                    if (!cellmodp->recursiveClone()) {
                        // In the non-Vrcm, which needs to point to Vrcm flavor
                        //
                        // Make a clone which this cell points to
                        // Later, the clone's cells will also point clone'd name
                        // This lets us link the XREFs between the (uncloned) children so
                        // they don't point to the same module which would
                        // break parameter resolution.
                        AstNodeModule* otherModp = VN_CAST(cellmodp->user2p(), NodeModule);
                        if (!otherModp) {
                            otherModp = cellmodp->cloneTree(false);
                            otherModp->name(otherModp->name() + "__Vrcm");
                            otherModp->user1p(nullptr);  // Need new vertex
                            otherModp->user2p(cellmodp);
                            otherModp->recursiveClone(true);
                            // user1 etc will retain its pre-clone value
                            cellmodp->user2p(otherModp);
                            v3Global.rootp()->addModulep(otherModp);
                            new V3GraphEdge(&m_graph, vertex(cellmodp), vertex(otherModp), 1,
                                            false);
                        }
                        cellmodp = otherModp;
                        nodep->modp(cellmodp);
                    } else {
                        // In the Vrcm, which needs to point back to Vrcm flavor
                        // The cell already has the correct resolution (to Vrcm)
                        nodep->modp(cellmodp);
                        // We don't create a V3GraphEdge (as it would be circular)
                    }
                } else {  // Non-recursive
                    // Track module depths, so can sort list from parent down to children
                    nodep->modp(cellmodp);
                    new V3GraphEdge(&m_graph, vertex(m_modp), vertex(cellmodp), 1, false);
                }
            }
        }
        // Remove AstCell(AstPin("",nullptr)), it's a side effect of how we parse "()"
        // the empty middle is identical to the empty rule that must find pins in "(,)".
        if (nodep->pinsp() && !nodep->pinsp()->nextp() && nodep->pinsp()->name() == ""
            && !nodep->pinsp()->exprp()) {
            pushDeletep(nodep->pinsp()->unlinkFrBackWithNext());
        }
        if (nodep->paramsp() && !nodep->paramsp()->nextp() && nodep->paramsp()->name() == ""
            && !nodep->paramsp()->exprp()) {
            pushDeletep(nodep->paramsp()->unlinkFrBackWithNext());
        }
        // Convert .* to list of pins
        bool pinStar = false;
        for (AstPin *nextp, *pinp = nodep->pinsp(); pinp; pinp = nextp) {
            nextp = VN_AS(pinp->nextp(), Pin);
            if (pinp->dotStar()) {
                if (pinStar) pinp->v3error("Duplicate .* in an instance");
                pinStar = true;
                // Done with this fake pin
                VL_DO_DANGLING(pinp->unlinkFrBack()->deleteTree(), pinp);
            }
        }
        // Convert unnamed pins to pin number based assignments
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->name() == "") pinp->name("__pinNumber" + cvtToStr(pinp->pinNum()));
        }
        for (AstPin* pinp = nodep->paramsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinp->param(true);
            if (pinp->name() == "") pinp->name("__paramNumber" + cvtToStr(pinp->pinNum()));
        }
        if (nodep->modp()) {
            nodep->modName(nodep->modp()->name());
            // Note what pins exist
            std::unordered_set<string> ports;  // Symbol table of all connected port names
            for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (pinp->name() == "")
                    pinp->v3error("Connect by position is illegal in .* connected instances");
                if (!pinp->exprp()) {
                    if (pinp->name().substr(0, 11) == "__pinNumber") {
                        pinp->v3warn(PINNOCONNECT,
                                     "Cell pin is not connected: " << pinp->prettyNameQ());
                    } else {
                        pinp->v3warn(PINCONNECTEMPTY,
                                     "Cell pin connected by name with empty reference: "
                                         << pinp->prettyNameQ());
                    }
                }
                ports.insert(pinp->name());
            }
            // We search ports, rather than in/out declarations as they aren't resolved yet,
            // and it's easier to do it now than in V3LinkDot when we'd need to repeat steps.
            for (AstNode* portnodep = nodep->modp()->stmtsp(); portnodep;
                 portnodep = portnodep->nextp()) {
                if (const AstPort* const portp = VN_CAST(portnodep, Port)) {
                    if (ports.find(portp->name()) == ports.end()
                        && ports.find("__pinNumber" + cvtToStr(portp->pinNum())) == ports.end()) {
                        if (pinStar) {
                            UINFO(9, "    need .* PORT  " << portp << endl);
                            // Create any not already connected
                            AstPin* const newp = new AstPin(
                                nodep->fileline(), 0, portp->name(),
                                new AstParseRef(nodep->fileline(), VParseRefExp::PX_TEXT,
                                                portp->name(), nullptr, nullptr));
                            newp->svImplicit(true);
                            nodep->addPinsp(newp);
                        } else {  // warn on the CELL that needs it, not the port
                            nodep->v3warn(PINMISSING,
                                          "Cell has missing pin: " << portp->prettyNameQ());
                            AstPin* const newp
                                = new AstPin(nodep->fileline(), 0, portp->name(), nullptr);
                            nodep->addPinsp(newp);
                        }
                    }
                }
            }
        }
        if (VN_IS(nodep->modp(), Iface)) {
            // Cell really is the parent's instantiation of an interface, not a normal module
            // Make sure we have a variable to refer to this cell, so can <ifacename>.<innermember>
            // in the same way that a child does.  Rename though to avoid conflict with cell.
            // This is quite similar to how classes work; when unpacked
            // classes are better supported may remap interfaces to be more
            // like a class.
            if (!nodep->hasIfaceVar()) {
                const string varName
                    = nodep->name() + "__Viftop";  // V3LinkDot looks for this naming
                AstIfaceRefDType* const idtypep = new AstIfaceRefDType(
                    nodep->fileline(), nodep->name(), nodep->modp()->name());
                idtypep->ifacep(nullptr);  // cellp overrides
                // In the case of arrayed interfaces, we replace cellp when de-arraying in V3Inst
                idtypep->cellp(nodep);  // Only set when real parent cell known.
                AstVar* varp;
                if (nodep->rangep()) {
                    AstNodeArrayDType* const arrp
                        = new AstUnpackArrayDType(nodep->fileline(), VFlagChildDType(), idtypep,
                                                  nodep->rangep()->cloneTree(true));
                    varp = new AstVar(nodep->fileline(), VVarType::IFACEREF, varName,
                                      VFlagChildDType(), arrp);
                } else {
                    varp = new AstVar(nodep->fileline(), VVarType::IFACEREF, varName,
                                      VFlagChildDType(), idtypep);
                }
                varp->isIfaceParent(true);
                nodep->addNextHere(varp);
                nodep->hasIfaceVar(true);
            }
        }
        if (nodep->modp()) {  //
            iterateChildren(nodep);
        }
        UINFO(4, " Link Cell done: " << nodep << endl);
    }

    virtual void visit(AstRefDType* nodep) override {
        iterateChildren(nodep);
        for (AstPin* pinp = nodep->paramsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinp->param(true);
            if (pinp->name() == "") pinp->name("__paramNumber" + cvtToStr(pinp->pinNum()));
        }
    }
    virtual void visit(AstClassOrPackageRef* nodep) override {
        iterateChildren(nodep);
        // Inside a class, an extends or reference to another class
        // Note we don't add a V3GraphEdge{vertex(m_modp), vertex(nodep->classOrPackagep()}
        // We could for an extends, but for another reference we cannot, as
        // it is legal to have classes both with parameters that link to each other
        for (AstPin* pinp = nodep->paramsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinp->param(true);
            if (pinp->name() == "") pinp->name("__paramNumber" + cvtToStr(pinp->pinNum()));
        }
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // METHODS
    void readModNames() {
        // mangled_name, BlockOptions
        const V3HierBlockOptSet& hierBlocks = v3Global.opt.hierBlocks();
        const auto hierIt = vlstd::as_const(hierBlocks).find(v3Global.opt.topModule());
        UASSERT((hierIt != hierBlocks.end()) == !!v3Global.opt.hierChild(),
                "information of the top module must exist if --hierarchical-child is set");
        // Look at all modules, and store pointers to all module names
        for (AstNodeModule *nextp, *nodep = v3Global.rootp()->modulesp(); nodep; nodep = nextp) {
            nextp = VN_AS(nodep->nextp(), NodeModule);
            if (v3Global.opt.hierChild() && nodep->name() == hierIt->second.origName()) {
                nodep->name(hierIt->first);  // Change name of this module to be mangled name
                                             // considering parameter
            }
            const AstNodeModule* const foundp = findModuleSym(nodep->name());
            if (foundp && foundp != nodep) {
                if (!(foundp->fileline()->warnIsOff(V3ErrorCode::MODDUP)
                      || nodep->fileline()->warnIsOff(V3ErrorCode::MODDUP)
                      || hierBlocks.find(nodep->name()) != hierBlocks.end())) {
                    nodep->v3warn(MODDUP, "Duplicate declaration of module: "
                                              << nodep->prettyNameQ() << '\n'
                                              << nodep->warnContextPrimary() << '\n'
                                              << foundp->warnOther()
                                              << "... Location of original declaration\n"
                                              << foundp->warnContextSecondary());
                }
                nodep->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (!foundp) {
                m_mods.rootp()->insert(nodep->name(), new VSymEnt(&m_mods, nodep));
            }
        }
        // if (debug() >= 9) m_mods.dump(cout, "-syms: ");
    }

public:
    // CONSTRUCTORS
    LinkCellsVisitor(AstNetlist* nodep, VInFilter* filterp, V3ParseSym* parseSymp)
        : m_filterp{filterp}
        , m_parseSymp{parseSymp}
        , m_mods{nodep} {
        if (v3Global.opt.hierChild()) {
            const V3HierBlockOptSet& hierBlocks = v3Global.opt.hierBlocks();
            UASSERT(!v3Global.opt.topModule().empty(),
                    "top module must be explicitly specified in hierarchical mode");
            const V3HierBlockOptSet::const_iterator hierIt
                = hierBlocks.find(v3Global.opt.topModule());
            UASSERT(hierIt != hierBlocks.end(),
                    "top module must be listed in --hierarchical-block");
            m_origTopModuleName = hierIt->second.origName();
        } else {
            m_origTopModuleName = v3Global.opt.topModule();
        }
        iterate(nodep);
    }
    virtual ~LinkCellsVisitor() override = default;
};

//######################################################################
// Link class functions

void V3LinkCells::link(AstNetlist* nodep, VInFilter* filterp, V3ParseSym* parseSymp) {
    UINFO(4, __FUNCTION__ << ": " << endl);
    { LinkCellsVisitor{nodep, filterp, parseSymp}; }
}
