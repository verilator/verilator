// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Subgraph boundary metadata and phase checks
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

// Record elaborated ports and connections as values, carrying only numeric port
// identities on the AST. No expression or procedure pointers survive a pass.
// Resolve publication links after Scope/LinkDot and check them again after NBA
// lowering. Record direct RTL accesses before optimization creates cross-scope
// aliases. The scheduler still owns eligibility and capture/evaluate/publish.

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3SubgraphBoundary.h"

#include "V3EmitV.h"
#include "V3File.h"
#include "V3Stats.h"

#include <map>
#include <set>
#include <sstream>

VL_DEFINE_DEBUG_FUNCTIONS;

static bool isUnderScope(const AstScope* scopep, const AstScope* basep) {
    for (const AstScope* scanp = scopep; scanp; scanp = scanp->aboveScopep()) {
        if (scanp == basep) return true;
    }
    return false;
}

const AstVarRef* V3SubgraphBoundary::writtenCombinationalVarRef(const AstNodeExpr* lhsp) {
    const AstVarRef* resultp = nullptr;
    bool multiple = false;
    lhsp->foreach([&](const AstVarRef* refp) {
        if (!refp->access().isWriteOrRW()) return;
        if (resultp) multiple = true;
        resultp = refp;
    });
    return multiple ? nullptr : resultp;
}

struct V3SubgraphBoundary::Impl final {
    struct Port final {
        string m_specialization;  // Elaborated module specialization name
        string m_name;  // Original RTL port name
        int m_width = 0;  // Resolved connection width
        VDirection m_direction;  // Direction of the boundary port
        unsigned m_writes = 0;  // Number of RTL writes to this port
    };
    struct Connection final {
        string m_instance;  // RTL instance path for diagnostic output
        uint32_t m_portId = 0;  // Stable boundary port identity
        int m_width = 0;  // Resolved connection width
        string m_shape;  // Shape of the connected expression
        std::vector<string> m_references;  // RTL names referenced by the connection or event
        string m_expression;  // Connected expression before pin lowering
    };
    struct Event final {
        string m_specialization;  // Elaborated module specialization name
        VEdgeType m_edge;  // Event edge kind
        std::vector<string> m_references;  // RTL names referenced by the connection or event
    };
    std::vector<Port> m_ports{1};  // Zero is not a boundary port
    std::vector<Connection> m_connections;  // Connections captured before pin lowering
    std::vector<Event> m_events;  // Clock events captured before scheduling
    std::set<uint32_t> m_connectedOutputs;  // Output ports connected by at least one instance
    std::set<std::pair<const AstCell*, uint32_t>>
        m_connectedInstanceOutputs;  // Connected output ports for each instance
    std::map<std::pair<uint32_t, uint32_t>, int>
        m_scoped;  // Scoped variable counts indexed by boundary and port
    // Record RTL accesses before optimization creates cross-scope intermediate values.
    std::map<uint32_t, FileLine*> m_externalAccess;
    unsigned m_specializations = 0;  // Number of selected elaborated modules
    unsigned m_nbaAssignments = 0;  // Delayed assignment count in selected modules

    const Port& port(const AstVar* varp) const {
        const uint32_t id = varp->subgraphPortId();
        UASSERT_OBJ(id && id < m_ports.size(), varp, "Missing elaborated boundary port identity");
        return m_ports[id];
    }

    void publications(AstNetlist* netlistp, bool afterDelayed) {
        std::map<const AstVarScope*, unsigned> writers;
        std::map<const AstVarScope*, const AstVarScope*> sources;
        std::map<const AstVarScope*, const AstVarScope*> pre;
        std::map<const AstVarScope*, const AstVarScope*> post;
        netlistp->foreach([&](AstNodeAssign* assp) {
            const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
            const AstVarRef* const rhsp = VN_CAST(assp->rhsp(), VarRef);
            if (lhsp && lhsp->varp()->subgraphPublished()) {
                const AstVarScope* const publishedp = lhsp->varScopep();
                UASSERT_OBJ(publishedp, lhsp, "Unresolved boundary publication");
                ++writers[publishedp];
                if (rhsp) sources.emplace(publishedp, rhsp->varScopep());
                if (!afterDelayed) {
                    UASSERT_OBJ(rhsp && rhsp->varScopep(), assp, "Unresolved publication source");
                    UASSERT_OBJ(rhsp->varp()->subgraphPortId() == lhsp->varp()->subgraphPortId(),
                                assp, "Publication connected to the wrong port");
                    UASSERT_OBJ(rhsp->varScopep()->scopep() == publishedp->scopep(), assp,
                                "Publication connected to the wrong instance");
                }
            }
        });
        const auto collectPairs = [](AstNode* nodep, auto& pairs) {
            nodep->foreach([&](AstAssign* assp) {
                const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
                const AstVarRef* const rhsp = VN_CAST(assp->rhsp(), VarRef);
                if (lhsp && rhsp) pairs.emplace(lhsp->varScopep(), rhsp->varScopep());
            });
        };
        netlistp->foreach([&](AstAlwaysPre* nodep) { collectPairs(nodep, pre); });
        netlistp->foreach([&](AstAlwaysPost* nodep) { collectPairs(nodep, post); });
        unsigned publications = 0;
        netlistp->foreach([&](AstVarScope* vscp) {
            if (!vscp->varp()->subgraphPublished()) return;
            const Port& metadata = port(vscp->varp());
            const std::pair<uint32_t, uint32_t> key{vscp->scopep()->subgraphInstanceId(),
                                                    vscp->varp()->subgraphPortId()};
            const std::pair<const AstCell*, uint32_t> connection{vscp->scopep()->aboveCellp(),
                                                                 vscp->varp()->subgraphPortId()};
            // Later checks use the instance/port identity resolved after Scope.
            const bool connected = afterDelayed ? m_scoped.count(key)
                                                : m_connectedInstanceOutputs.count(connection);
            if (!connected) {
                UASSERT_OBJ(writers[vscp] == 0, vscp,
                            "Unconnected boundary output has a publication driver");
                return;
            }
            UASSERT_OBJ(m_connectedOutputs.count(vscp->varp()->subgraphPortId()), vscp,
                        "Publication has no prepared output connection");
            UASSERT_OBJ(metadata.m_direction == VDirection::OUTPUT, vscp,
                        "Published boundary is not an output");
            UASSERT_OBJ(metadata.m_width == vscp->width(), vscp,
                        "Boundary publication width changed");
            UASSERT_OBJ(vscp->scopep()->modp()->subgraphBoundary(), vscp,
                        "Publication escaped its boundary scope");
            UASSERT_OBJ(writers[vscp] == 1, vscp, "Boundary publication must have one driver");
            if (!afterDelayed) {
                UASSERT_OBJ(m_scoped.emplace(key, vscp->width()).second, vscp,
                            "Duplicate boundary publication identity");
            }
            ++publications;
        });
        unsigned nbaPairs = 0;
        unsigned nbaPublications = 0;
        if (afterDelayed) {
            std::map<const AstVarScope*, const AstVarScope*> representativeState;
            netlistp->foreach([&](AstScope* scopep) {
                AstScope* const implementationp = scopep->subgraphImplementationScopep();
                if (!implementationp) return;
                std::map<const AstVar*, const AstVarScope*> implementationVars;
                for (AstVarScope* vscp = implementationp->varsp(); vscp;
                     vscp = VN_AS(vscp->nextp(), VarScope)) {
                    implementationVars.emplace(vscp->varp(), vscp);
                }
                for (AstVarScope* vscp = scopep->varsp(); vscp;
                     vscp = VN_AS(vscp->nextp(), VarScope)) {
                    const auto it = implementationVars.find(vscp->varp());
                    if (it != implementationVars.end()) {
                        representativeState.emplace(vscp, it->second);
                    }
                }
            });
            for (const auto& pair : post) {
                const auto it = pre.find(pair.second);
                if (it == pre.end()) continue;  // Other NBA lowering schemes have no shadow pre
                UASSERT_OBJ(it->second == pair.first, pair.first,
                            "NBA pre/post pair refers to different state");
                if (!pair.first->scopep()->modp()->subgraphBoundary()) continue;
                UASSERT_OBJ(pair.second->scopep() == pair.first->scopep(), pair.first,
                            "NBA shadow escaped the boundary instance");
                ++nbaPairs;
            }
            for (const auto& pair : representativeState) {
                const auto it = post.find(pair.second);
                if (it != post.end() && pre.count(it->second)) ++nbaPairs;
            }
            V3Stats::addStat("Subgraph boundary, NBA shadow pairs", nbaPairs);
            for (const auto& source : sources) {
                const auto representative = representativeState.find(source.second);
                const AstVarScope* const statep = representative == representativeState.end()
                                                      ? source.second
                                                      : representative->second;
                const auto it = post.find(statep);
                if (it == post.end() || !pre.count(it->second)) continue;
                UASSERT_OBJ(isUnderScope(source.second->scopep(), source.first->scopep()),
                            source.first,
                            "Published NBA state belongs to a different boundary instance");
                ++nbaPublications;
            }
            V3Stats::addStat("Subgraph boundary, NBA publications", nbaPublications);
        }
        V3Stats::addStat(afterDelayed ? "Subgraph boundary, delayed publications"
                                      : "Subgraph boundary, scoped publications",
                         publications);
    }

    void dump() const {
        if (!v3Global.opt.stats()) return;
        const std::unique_ptr<std::ofstream> osp{V3File::new_ofstream(
            v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__subgraph_boundary.txt")};
        // Preserve source identities for inspection, including with --protect-ids.
        for (size_t id = 1; id < m_ports.size(); ++id) {
            const Port& entry = m_ports[id];
            *osp << "port " << id << " width=" << entry.m_width
                 << " direction=" << entry.m_direction.ascii() << " writes=" << entry.m_writes
                 << " specialization=" << VIdProtect::protect(entry.m_specialization)
                 << " name=" << VIdProtect::protect(entry.m_name) << '\n';
        }
        for (const Event& event : m_events) {
            *osp << "event " << event.m_edge.ascii() << " references=" << event.m_references.size()
                 << " specialization=" << VIdProtect::protect(event.m_specialization) << '\n';
        }
        for (const Connection& connection : m_connections) {
            *osp << "connection port=" << connection.m_portId << " width=" << connection.m_width
                 << " shape=" << connection.m_shape
                 << " references=" << connection.m_references.size()
                 << " instance=" << VIdProtect::protect(connection.m_instance) << " expression="
                 << V3OutFormatter::quoteNameControls(
                        VIdProtect::protectWordsIf(connection.m_expression))
                 << '\n';
        }
    }
};

V3SubgraphBoundary::V3SubgraphBoundary(AstNetlist* netlistp)
    : m_impl{new Impl} {
    if (!v3Global.opt.subgraphSchedule()) return;
    netlistp->foreach([&](AstNodeModule* modp) {
        if (!modp->subgraphBoundary()) return;
        ++m_impl->m_specializations;
        modp->foreach([&](AstVar* varp) {
            if (!varp->isIO() || varp->isFuncLocal()) return;
            varp->subgraphPortId(m_impl->m_ports.size());
            m_impl->m_ports.push_back(
                {modp->name(), varp->name(), varp->width(), varp->direction(), 0});
        });
        modp->foreach([&](AstNodeVarRef* refp) {
            if (!refp->varp()->subgraphPortId() || !refp->access().isWriteOrRW()) return;
            ++m_impl->m_ports[refp->varp()->subgraphPortId()].m_writes;
        });
        modp->foreach([&](AstAssignDly*) { ++m_impl->m_nbaAssignments; });
        modp->foreach([&](AstSenItem* senp) {
            Impl::Event event{modp->name(), senp->edgeType(), {}};
            senp->foreach(
                [&](AstNodeVarRef* refp) { event.m_references.push_back(refp->varp()->name()); });
            m_impl->m_events.emplace_back(std::move(event));
        });
    });
    V3Stats::addStat("Subgraph boundary, elaborated specializations", m_impl->m_specializations);
    V3Stats::addStat("Subgraph boundary, elaborated ports", m_impl->m_ports.size() - 1);
    V3Stats::addStat("Subgraph boundary, elaborated NBA assignments", m_impl->m_nbaAssignments);
    V3Stats::addStat("Subgraph boundary, elaborated events", m_impl->m_events.size());
}

V3SubgraphBoundary::~V3SubgraphBoundary() = default;

void V3SubgraphBoundary::prepare(AstNetlist* netlistp) {
    if (!v3Global.opt.subgraphSchedule()) return;
    netlistp->foreach([&](AstCell* cellp) {
        if (!cellp->modp()->subgraphBoundary()) return;
        for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            const AstVar* const portp = pinp->modVarp();
            // Interfaces and generated tristate ports are handled by the normal Inst path.
            if (!portp->subgraphPortId()) continue;
            const Impl::Port& metadata = m_impl->port(portp);
            UASSERT_OBJ(metadata.m_width == portp->width(), pinp,
                        "Boundary port width changed before Inst");
            UASSERT_OBJ(metadata.m_direction == portp->direction(), pinp,
                        "Boundary port direction changed before Inst");
            if (!pinp->exprp()) continue;
            if (metadata.m_direction == VDirection::OUTPUT) {
                m_impl->m_connectedOutputs.insert(portp->subgraphPortId());
                m_impl->m_connectedInstanceOutputs.emplace(cellp, portp->subgraphPortId());
            }
            Impl::Connection connection{cellp->name(),
                                        portp->subgraphPortId(),
                                        pinp->exprp()->width(),
                                        pinp->exprp()->typeName(),
                                        {},
                                        ""};
            std::ostringstream expression;
            V3EmitV::verilogForTree(pinp->exprp(), expression);
            connection.m_expression = expression.str();
            pinp->exprp()->foreach([&](AstNodeVarRef* refp) {
                connection.m_references.push_back(refp->varp()->name());
            });
            m_impl->m_connections.emplace_back(std::move(connection));
        }
    });
    V3Stats::addStat("Subgraph boundary, prepared connections", m_impl->m_connections.size());
    m_impl->dump();
}

void V3SubgraphBoundary::scoped(AstNetlist* netlistp) {
    if (!v3Global.opt.subgraphSchedule()) return;
    uint32_t nextId = 0;
    netlistp->foreach([&](AstScope* scopep) {
        if (!scopep->modp()->subgraphBoundary()) return;
        scopep->subgraphInstanceId(++nextId);
    });
    // Inst creates the port-to-publication copy in the parent scope. These two
    // references implement the boundary contract rather than bypassing it.
    std::set<const AstNodeVarRef*> publicationRefs;
    netlistp->foreach([&](AstNodeAssign* assp) {
        const AstVarRef* const lhsp = VN_CAST(assp->lhsp(), VarRef);
        const AstVarRef* const rhsp = VN_CAST(assp->rhsp(), VarRef);
        if (!lhsp || !rhsp || !lhsp->varp()->subgraphPublished()) return;
        publicationRefs.insert(lhsp);
        publicationRefs.insert(rhsp);
    });
    netlistp->foreach([&](AstScope* scopep) {
        scopep->foreach([&](AstNodeVarRef* refp) {
            if (publicationRefs.count(refp)) return;
            AstScope* boundaryp = refp->varScopep()->scopep();
            while (boundaryp && !boundaryp->modp()->subgraphBoundary()) {
                boundaryp = boundaryp->aboveScopep();
            }
            if (!boundaryp || isUnderScope(scopep, boundaryp)) return;
            const AstVar* const varp = refp->varp();
            const bool inputWrite = varp->isInput() && refp->access().isWriteOnly();
            const bool captureWrite = varp->subgraphCaptured() && refp->access().isWriteOnly();
            const bool outputRead = varp->subgraphPublished() && refp->access().isReadOnly();
            if (inputWrite || captureWrite || outputRead) return;
            AstScope* const implementationp = boundaryp->subgraphImplementationScopep()
                                                  ? boundaryp->subgraphImplementationScopep()
                                                  : boundaryp;
            m_impl->m_externalAccess.emplace(implementationp->subgraphInstanceId(),
                                             refp->fileline());
        });
    });
    V3Stats::addStat("Subgraph boundary, resolved instances", nextId);
    m_impl->publications(netlistp, false);
}

FileLine* V3SubgraphBoundary::externalAccessFileline(const AstScope* scopep) const {
    const auto it = m_impl->m_externalAccess.find(scopep->subgraphInstanceId());
    return it == m_impl->m_externalAccess.end() ? nullptr : it->second;
}

void V3SubgraphBoundary::delayed(AstNetlist* netlistp) {
    if (v3Global.opt.subgraphSchedule()) m_impl->publications(netlistp, true);
}

void V3SubgraphBoundary::scheduled(AstNetlist* netlistp) {
    if (!v3Global.opt.subgraphSchedule()) return;
    std::set<const AstCFunc*> called;
    netlistp->foreach([&](AstCCall* callp) { called.insert(callp->funcp()); });
    unsigned wrappers = 0;
    netlistp->foreach([&](AstCFunc* funcp) {
        if (!funcp->subgraphWrapper()) return;
        UASSERT_OBJ(called.count(funcp), funcp, "Subgraph evaluation has no caller");
        ++wrappers;
    });
    netlistp->foreach([](AstActive* activep) {
        UASSERT_OBJ(!activep->stmtsp(), activep, "Unconsumed logic after subgraph scheduling");
    });
    V3Stats::addStat("Subgraph boundary, connected wrappers", wrappers);
}
