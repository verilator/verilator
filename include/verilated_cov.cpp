// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2020 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
//=============================================================================
///
/// \file
/// \brief Verilator coverage analysis
///
//=============================================================================

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_cov.h"
#include "verilated_cov_key.h"

#include <deque>
#include <fstream>
#include <map>

//=============================================================================
// VerilatedCovImpBase
/// Implementation base class for constants

struct VerilatedCovImpBase {
    // TYPES
    enum { MAX_KEYS = 33 };  /// Maximum user arguments + filename+lineno
    enum { KEY_UNDEF = 0 };  /// Magic key # for unspecified values
};

//=============================================================================
// VerilatedCovImpItem
/// Implementation class for a VerilatedCov item

class VerilatedCovImpItem : VerilatedCovImpBase {
public:  // But only local to this file
    // MEMBERS
    int m_keys[MAX_KEYS];  ///< Key
    int m_vals[MAX_KEYS];  ///< Value for specified key
    // CONSTRUCTORS
    // Derived classes should call zero() in their constructor
    VerilatedCovImpItem() {
        for (int i=0; i<MAX_KEYS; ++i) {
            m_keys[i] = KEY_UNDEF;
            m_vals[i] = 0;
        }
    }
    virtual ~VerilatedCovImpItem() {}
    virtual vluint64_t count() const = 0;
    virtual void zero() const = 0;
};

//=============================================================================
/// VerilatedCoverItem templated for a specific class
/// Creates a new coverage item for the specified type.
/// This isn't in the header file for auto-magic conversion because it
/// inlines to too much code and makes compilation too slow.

template <class T> class VerilatedCoverItemSpec : public VerilatedCovImpItem {
private:
    // MEMBERS
    T*  m_countp;  ///< Count value
public:
    // METHODS
    // cppcheck-suppress truncLongCastReturn
    virtual vluint64_t count() const VL_OVERRIDE { return *m_countp; }
    virtual void zero() const VL_OVERRIDE { *m_countp = 0; }
    // CONSTRUCTORS
    // cppcheck-suppress noExplicitConstructor
    VerilatedCoverItemSpec(T* countp) : m_countp(countp) { *m_countp = 0; }
    virtual ~VerilatedCoverItemSpec() VL_OVERRIDE {}
};

//=============================================================================
// VerilatedCovImp
/// Implementation class for VerilatedCov.  See that class for public method information.
/// All value and keys are indexed into a unique number.  Thus we can greatly reduce
/// the storage requirements for otherwise identical keys.

class VerilatedCovImp : VerilatedCovImpBase {
private:
    // TYPES
    typedef std::map<std::string,int> ValueIndexMap;
    typedef std::map<int,std::string> IndexValueMap;
    typedef std::deque<VerilatedCovImpItem*> ItemList;

private:
    // MEMBERS
    VerilatedMutex      m_mutex;  ///< Protects all members, when VL_THREADED. Wrapper deals with setting it.
    ValueIndexMap       m_valueIndexes VL_GUARDED_BY(m_mutex);  ///< For each key/value a unique arbitrary index value
    IndexValueMap       m_indexValues VL_GUARDED_BY(m_mutex);  ///< For each key/value a unique arbitrary index value
    ItemList            m_items VL_GUARDED_BY(m_mutex);  ///< List of all items

    VerilatedCovImpItem* m_insertp VL_GUARDED_BY(m_mutex);  ///< Item about to insert
    const char*         m_insertFilenamep VL_GUARDED_BY(m_mutex);  ///< Filename about to insert
    int                 m_insertLineno VL_GUARDED_BY(m_mutex);  ///< Line number about to insert

    // CONSTRUCTORS
    VerilatedCovImp() {
        m_insertp = NULL;
        m_insertFilenamep = NULL;
        m_insertLineno = 0;
    }
    VL_UNCOPYABLE(VerilatedCovImp);
public:
    ~VerilatedCovImp() { clearGuts(); }
    static VerilatedCovImp& imp() VL_MT_SAFE {
        static VerilatedCovImp s_singleton;
        return s_singleton;
    }

private:
    // PRIVATE METHODS
    int valueIndex(const std::string& value) VL_REQUIRES(m_mutex) {
        static int nextIndex = KEY_UNDEF+1;
        ValueIndexMap::iterator iter = m_valueIndexes.find(value);
        if (iter != m_valueIndexes.end()) return iter->second;
        nextIndex++;  assert(nextIndex>0);
        m_valueIndexes.insert(std::make_pair(value, nextIndex));
        m_indexValues.insert(std::make_pair(nextIndex, value));
        return nextIndex;
    }
    static std::string dequote(const std::string& text) VL_PURE {
        // Quote any special characters
        std::string rtn;
        for (const char* pos = text.c_str(); *pos; ++pos) {
            if (!isprint(*pos) || *pos=='%' || *pos=='"') {
                char hex[10]; sprintf(hex, "%%%02X", pos[0]);
                rtn += hex;
            } else {
                rtn += *pos;
            }
        }
        return rtn;
    }
    static bool legalKey(const std::string& key) VL_PURE {
        // Because we compress long keys to a single letter, and
        // don't want applications to either get confused if they use
        // a letter differently, nor want them to rely on our compression...
        // (Considered using numeric keys, but will remain back compatible.)
        if (key.length()<2) return false;
        if (key.length()==2 && isdigit(key[1])) return false;
        return true;
    }
    static std::string keyValueFormatter(const std::string& key, const std::string& value) VL_PURE {
        std::string name;
        if (key.length()==1 && isalpha(key[0])) {
            name += std::string("\001")+key;
        } else {
            name += std::string("\001")+dequote(key);
        }
        name += std::string("\002")+dequote(value);
        return name;
    }
    static std::string combineHier(const std::string& old, const std::string& add) VL_PURE {
        // (foo.a.x, foo.b.x) => foo.*.x
        // (foo.a.x, foo.b.y) => foo.*
        // (foo.a.x, foo.b)   => foo.*
        if (old == add) return add;
        if (old.empty()) return add;
        if (add.empty()) return old;

        const char* a = old.c_str();
        const char* b = add.c_str();

        // Scan forward to first mismatch
        const char* apre = a;
        const char* bpre = b;
        while (*apre == *bpre) { apre++; bpre++; }

        // We used to backup and split on only .'s but it seems better to be verbose
        // and not assume . is the separator
        std::string prefix = std::string(a, apre-a);

        // Scan backward to last mismatch
        const char* apost = a+strlen(a)-1;
        const char* bpost = b+strlen(b)-1;
        while (*apost == *bpost
               && apost>apre && bpost>bpre) { apost--; bpost--; }

        // Forward to . so we have a whole word
        std::string suffix = *bpost ? std::string(bpost+1) : "";

        std::string out = prefix+"*"+suffix;

        //cout << "\nch pre="<<prefix<<"  s="<<suffix<<"\nch a="<<old<<"\nch b="<<add<<"\nch o="<<out<<endl;
        return out;
    }
    bool itemMatchesString(VerilatedCovImpItem* itemp, const std::string& match) VL_REQUIRES(m_mutex) {
        for (int i=0; i<MAX_KEYS; ++i) {
            if (itemp->m_keys[i] != KEY_UNDEF) {
                // We don't compare keys, only values
                std::string val = m_indexValues[itemp->m_vals[i]];
                if (std::string::npos != val.find(match)) {  // Found
                    return true;
                }
            }
        }
        return false;
    }
    static void selftest() VL_MT_SAFE {
        // Little selftest
        if (combineHier("a.b.c","a.b.c")     !="a.b.c") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("a.b.c","a.b")       !="a.b*") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("a.x.c","a.y.c")     !="a.*.c") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("a.z.z.z.c","a.b.c") !="a.*.c") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("z","a")             !="*") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("q.a","q.b")         !="q.*") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("q.za","q.zb")       !="q.z*") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
        if (combineHier("1.2.3.a","9.8.7.a") !="*.a") VL_FATAL_MT(__FILE__,__LINE__,"","%Error: selftest\n");
    }
    void clearGuts() VL_REQUIRES(m_mutex) {
        for (ItemList::const_iterator it=m_items.begin(); it!=m_items.end(); ++it) {
            VerilatedCovImpItem* itemp = *(it);
            VL_DO_DANGLING(delete itemp, itemp);
        }
        m_items.clear();
        m_indexValues.clear();
        m_valueIndexes.clear();
    }

public:
    // PUBLIC METHODS
    void clear() VL_EXCLUDES(m_mutex) {
        Verilated::quiesce();
        VerilatedLockGuard lock(m_mutex);
        clearGuts();
    }
    void clearNonMatch(const char* matchp) VL_EXCLUDES(m_mutex) {
        Verilated::quiesce();
        VerilatedLockGuard lock(m_mutex);
        if (matchp && matchp[0]) {
            ItemList newlist;
            for (ItemList::iterator it=m_items.begin(); it!=m_items.end(); ++it) {
                VerilatedCovImpItem* itemp = *(it);
                if (!itemMatchesString(itemp, matchp)) {
                    VL_DO_DANGLING(delete itemp, itemp);
                } else {
                    newlist.push_back(itemp);
                }
            }
            m_items = newlist;
        }
    }
    void zero() VL_EXCLUDES(m_mutex) {
        Verilated::quiesce();
        VerilatedLockGuard lock(m_mutex);
        for (ItemList::const_iterator it=m_items.begin(); it!=m_items.end(); ++it) {
            (*it)->zero();
        }
    }

    // We assume there's always call to i/f/p in that order
    void inserti(VerilatedCovImpItem* itemp) VL_EXCLUDES(m_mutex) {
        VerilatedLockGuard lock(m_mutex);
        assert(!m_insertp);
        m_insertp = itemp;
    }
    void insertf(const char* filenamep, int lineno) VL_EXCLUDES(m_mutex) {
        VerilatedLockGuard lock(m_mutex);
        m_insertFilenamep = filenamep;
        m_insertLineno = lineno;
    }
    void insertp(const char* ckeyps[MAX_KEYS],
                 const char* valps[MAX_KEYS]) VL_EXCLUDES(m_mutex) {
        VerilatedLockGuard lock(m_mutex);
        assert(m_insertp);
        // First two key/vals are filename
        ckeyps[0]="filename";   valps[0]=m_insertFilenamep;
        std::string linestr = vlCovCvtToStr(m_insertLineno);
        ckeyps[1]="lineno";     valps[1]=linestr.c_str();
        // Default page if not specified
        const char* fnstartp = m_insertFilenamep;
        while (const char* foundp = strchr(fnstartp,'/')) fnstartp = foundp+1;
        const char* fnendp = fnstartp;
        while (*fnendp && *fnendp!='.') fnendp++;
        std::string page_default = "sp_user/"+std::string(fnstartp, fnendp-fnstartp);
        ckeyps[2]="page";       valps[2]=page_default.c_str();

        // Keys -> strings
        std::string keys[MAX_KEYS];
        for (int i=0; i<MAX_KEYS; ++i) {
            if (ckeyps[i] && ckeyps[i][0]) {
                keys[i] = ckeyps[i];
            }
        }
        // Ignore empty keys
        for (int i=0; i<MAX_KEYS; ++i) {
            if (!keys[i].empty()) {
                for (int j=i+1; j<MAX_KEYS; ++j) {
                    if (keys[i] == keys[j]) {  // Duplicate key.  Keep the last one
                        keys[i] = "";
                        break;
                    }
                }
            }
        }
        // Insert the values
        int addKeynum = 0;
        for (int i=0; i<MAX_KEYS; ++i) {
            const std::string key = keys[i];
            if (!keys[i].empty()) {
                const std::string val = valps[i];
                //cout<<"   "<<__FUNCTION__<<"  "<<key<<" = "<<val<<endl;
                m_insertp->m_keys[addKeynum] = valueIndex(key);
                m_insertp->m_vals[addKeynum] = valueIndex(val);
                addKeynum++;
                if (!legalKey(key)) {
                    std::string msg
                        = ("%Error: Coverage keys of one character, or letter+digit are illegal: "
                           +key);
                    VL_FATAL_MT("", 0, "", msg.c_str());
                }
            }
        }
        m_items.push_back(m_insertp);
        // Prepare for next
        m_insertp = NULL;
    }

    void write(const char* filename) VL_EXCLUDES(m_mutex) {
        Verilated::quiesce();
        VerilatedLockGuard lock(m_mutex);
#ifndef VM_COVERAGE
        VL_FATAL_MT("", 0, "", "%Error: Called VerilatedCov::write when VM_COVERAGE disabled\n");
#endif
        selftest();

        std::ofstream os(filename);
        if (os.fail()) {
            std::string msg = std::string("%Error: Can't write '")+filename+"'";
            VL_FATAL_MT("", 0, "", msg.c_str());
            return;
        }
        os << "# SystemC::Coverage-3\n";

        // Build list of events; totalize if collapsing hierarchy
        typedef std::map<std::string,std::pair<std::string,vluint64_t> > EventMap;
        EventMap eventCounts;
        for (ItemList::iterator it=m_items.begin(); it!=m_items.end(); ++it) {
            VerilatedCovImpItem* itemp = *(it);
            std::string name;
            std::string hier;
            bool per_instance = false;

            for (int i=0; i<MAX_KEYS; ++i) {
                if (itemp->m_keys[i] != KEY_UNDEF) {
                    std::string key = VerilatedCovKey::shortKey(m_indexValues[itemp->m_keys[i]]);
                    std::string val = m_indexValues[itemp->m_vals[i]];
                    if (key == VL_CIK_PER_INSTANCE) {
                        if (val != "0") per_instance = true;
                    }
                    if (key == VL_CIK_HIER) {
                        hier = val;
                    } else {
                        // Print it
                        name += keyValueFormatter(key, val);
                    }
                }
            }
            if (per_instance) {  // Not collapsing hierarchies
                name += keyValueFormatter(VL_CIK_HIER, hier);
                hier = "";
            }

            // Group versus point labels don't matter here, downstream
            // deals with it.  Seems bad for sizing though and doesn't
            // allow easy addition of new group codes (would be
            // inefficient)

            // Find or insert the named event
            EventMap::iterator cit = eventCounts.find(name);
            if (cit != eventCounts.end()) {
                const std::string& oldhier = cit->second.first;
                cit->second.second += itemp->count();
                cit->second.first  = combineHier(oldhier, hier);
            } else {
                eventCounts.insert(std::make_pair(name, make_pair(hier, itemp->count())));
            }
        }

        // Output body
        for (EventMap::const_iterator it=eventCounts.begin(); it!=eventCounts.end(); ++it) {
            os<<"C '"<<std::dec;
            os<<it->first;
            if (!it->second.first.empty()) os<<keyValueFormatter(VL_CIK_HIER, it->second.first);
            os<<"' "<<it->second.second;
            os<<std::endl;
        }
    }
};

//=============================================================================
// VerilatedCov

void VerilatedCov::clear() VL_MT_SAFE {
    VerilatedCovImp::imp().clear();
}
void VerilatedCov::clearNonMatch(const char* matchp) VL_MT_SAFE {
    VerilatedCovImp::imp().clearNonMatch(matchp);
}
void VerilatedCov::zero() VL_MT_SAFE {
    VerilatedCovImp::imp().zero();
}
void VerilatedCov::write(const char* filenamep) VL_MT_SAFE {
    VerilatedCovImp::imp().write(filenamep);
}
void VerilatedCov::_inserti(vluint32_t* itemp) VL_MT_SAFE {
    VerilatedCovImp::imp().inserti(new VerilatedCoverItemSpec<vluint32_t>(itemp));
}
void VerilatedCov::_inserti(vluint64_t* itemp) VL_MT_SAFE {
    VerilatedCovImp::imp().inserti(new VerilatedCoverItemSpec<vluint64_t>(itemp));
}
void VerilatedCov::_insertf(const char* filename, int lineno) VL_MT_SAFE {
    VerilatedCovImp::imp().insertf(filename, lineno);
}

#define K(n) const char* key ## n
#define A(n) const char* key ## n, const char* valp ## n  // Argument list
#define C(n) key ## n, valp ## n  // Calling argument list
#define N(n) "",""  // Null argument list
void VerilatedCov::_insertp(A(0),A(1),A(2),A(3),A(4),A(5),A(6),A(7),A(8),A(9),
                            A(10),A(11),A(12),A(13),A(14),A(15),A(16),A(17),A(18),A(19),
                            A(20),A(21),A(22),A(23),A(24),A(25),A(26),A(27),A(28),A(29)) VL_MT_SAFE {
    const char* keyps[VerilatedCovImpBase::MAX_KEYS]
        = {NULL,NULL,NULL,  // filename,lineno,page
           key0,key1,key2,key3,key4,key5,key6,key7,key8,key9,
           key10,key11,key12,key13,key14,key15,key16,key17,key18,key19,
           key20,key21,key22,key23,key24,key25,key26,key27,key28,key29};
    const char* valps[VerilatedCovImpBase::MAX_KEYS]
        = {NULL,NULL,NULL,  // filename,lineno,page
           valp0,valp1,valp2,valp3,valp4,valp5,valp6,valp7,valp8,valp9,
           valp10,valp11,valp12,valp13,valp14,valp15,valp16,valp17,valp18,valp19,
           valp20,valp21,valp22,valp23,valp24,valp25,valp26,valp27,valp28,valp29};
    VerilatedCovImp::imp().insertp(keyps, valps);
}

// And versions with fewer arguments  (oh for a language with named parameters!)
void VerilatedCov::_insertp(A(0),A(1),A(2),A(3),A(4),A(5),A(6),A(7),A(8),A(9)) VL_MT_SAFE {
    _insertp(C(0),C(1),C(2),C(3),C(4),C(5),C(6),C(7),C(8),C(9),
             N(10),N(11),N(12),N(13),N(14),N(15),N(16),N(17),N(18),N(19),
             N(20),N(21),N(22),N(23),N(24),N(25),N(26),N(27),N(28),N(29));
}
void VerilatedCov::_insertp(A(0),A(1),A(2),A(3),A(4),A(5),A(6),A(7),A(8),A(9),
                            A(10),A(11),A(12),A(13),A(14),A(15),A(16),A(17),A(18),A(19)) VL_MT_SAFE {
    _insertp(C(0),C(1),C(2),C(3),C(4),C(5),C(6),C(7),C(8),C(9),
             C(10),C(11),C(12),C(13),C(14),C(15),C(16),C(17),C(18),C(19),
             N(20),N(21),N(22),N(23),N(24),N(25),N(26),N(27),N(28),N(29));
}
// Backward compatibility for Verilator
void VerilatedCov::_insertp(A(0), A(1),  K(2),int val2,  K(3),int val3,
                            K(4),const std::string& val4,  A(5),A(6)) VL_MT_SAFE {
    std::string val2str = vlCovCvtToStr(val2);
    std::string val3str = vlCovCvtToStr(val3);
    _insertp(C(0),C(1),
             key2,val2str.c_str(),  key3,val3str.c_str(),  key4, val4.c_str(),
             C(5),C(6),N(7),N(8),N(9),
             N(10),N(11),N(12),N(13),N(14),N(15),N(16),N(17),N(18),N(19),
             N(20),N(21),N(22),N(23),N(24),N(25),N(26),N(27),N(28),N(29));
}
#undef A
#undef C
#undef N
#undef K
