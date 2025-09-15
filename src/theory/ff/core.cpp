/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields UNSAT core construction.
 *
 * Essentially a dependency graph for polynomials in the ideal.
 * It is a dependency graph for proofs in IdealCalc (Figure 4 from [OKTB23])
 *
 * Hooks into CoCoA.
 *
 * [OKTB23]: https://doi.org/10.1007/978-3-031-37703-7_8
 */

#ifdef CVC5_USE_COCOA

#include "theory/rewriter.h"

#include "theory/ff/core.h"

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/library.H>

#include <sstream>

#include "smt/assertions.h"
#include "theory/ff/cocoa_encoder.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

const std::string INPUT = "!!INPUT";

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

Tracer::Tracer(const std::vector<CoCoA::RingElem>& inputs)
    : d_inputNumbers()
{
  // Nethermind
  polynomials.push_back(Poly(ZERO));
  reductions.emplace(0, Reduction(0));
  p_input_size = inputs.size();

  for (size_t i = 0, end = inputs.size(); i < end; ++i)
  {
    const std::string s = ostring(inputs[i]);
    d_parents[s] = {};
    Trace("ff::trace") << "input: " << s << std::endl;
    d_inputNumbers.emplace(std::move(s), i);

    // Nethermind
    polynomials.push_back(Poly(inputs[i]));
  }
};

void Tracer::setFunctionPointers()
{
  Tracer* t = this;
  d_sPoly =
      std::function([=](CoCoA::ConstRefRingElem p,
                        CoCoA::ConstRefRingElem q,
                        CoCoA::ConstRefRingElem s) { t->sPoly(p, q, s); });
  d_reductionStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStart(p); });
  d_reductionStep =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStep(p); });
  d_reductionEnd =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionEnd(p); });
  Assert(!CoCoA::handlersEnabled);
  CoCoA::handlersEnabled = true;
  CoCoA::sPolyHandler = d_sPoly;
  CoCoA::reductionStartHandler = d_reductionStart;
  CoCoA::reductionStepHandler = d_reductionStep;
  CoCoA::reductionEndHandler = d_reductionEnd;
}

void Tracer::unsetFunctionPointers()
{
  CoCoA::handlersEnabled = false;
}

std::vector<size_t> Tracer::trace(const CoCoA::RingElem& i) const
{
  // accumulates ancestors of i that are inputs.
  std::vector<size_t> inputAncestors;
  // the q(ueue) contains transitive ancestors of i (initially just i) whose
  // parent relationships have not been visited yet.
  std::vector<std::string> q{ostring(i)};
  std::unordered_set<std::string> visited{q.back()};
  while (q.size())
  {
    const std::string t = q.back();
    Trace("ff::trace") << "traceback: " << t << std::endl;
    q.pop_back();
    // is the ancestor an input?
    if (d_inputNumbers.count(t))
    {
      // yes? output it
      Trace("ff::trace") << " blame" << std::endl;
      inputAncestors.push_back(d_inputNumbers.at(t));
    }
    else
    {
      // no? enqueue its parents
      AlwaysAssert(d_parents.count(t) > 0) << "Unexplained polynomial " << t;
      const auto& blames = d_parents.at(t);
      AlwaysAssert(blames.size() > 0) << "Unexplained polynomial " << t;
      for (const auto& b : blames)
      {
        if (!visited.count(b))
        {
          visited.insert(b);
          q.push_back(b);
        }
      }
    }
  }
  // sort outputs by index in initial input sequence and return
  std::sort(inputAncestors.begin(), inputAncestors.end());
  return inputAncestors;
}

void Tracer::sPoly(CoCoA::ConstRefRingElem p,
                              CoCoA::ConstRefRingElem q,
                              CoCoA::ConstRefRingElem s)
{
  std::string ss = ostring(s);
  Trace("ff::trace") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_parents.count(ss) == 0)
  {
    Trace("ff::trace") << " keep" << std::endl;
    addDep(ostring(p), ss);
    addDep(ostring(q), ss);
  }
  else
  {
    Trace("ff::trace") << " drop" << std::endl;
  }

  auto pi = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f.p, p); });
  Assert(pi != polynomials.end());
  auto qi = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f.p, q); });
  Assert(qi != polynomials.end()); 
  
  size_t index_p = std::distance(polynomials.begin(), pi);
  size_t index_q = std::distance(polynomials.begin(), qi);
  Trace("neth") << "(Core) sPoly: " << p << " (" << index_p << "), " << q << " (" << index_q << ") -> " << s << std::endl;
  polynomials.push_back(Poly(s, p, q));
}

void Tracer::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::trace") << "reduction start: " << p << std::endl;
  d_reductionSeq.push_back(ostring(p));

  auto pi = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f.p, p); });
  Assert(pi != polynomials.end());
  size_t index = std::distance(polynomials.begin(), pi); 
  currentReduction = Reduction(index);
  Trace("neth") << "(Core) reduction: " << p << " (" << index << ")" << std::endl;
}

void Tracer::reductionStep(CoCoA::ConstRefRingElem q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace::step") << "reduction step: " << q << std::endl;
  d_reductionSeq.push_back(ostring(q));

  auto qi = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f.p, q); });
  Trace("neth") << "reduction step: " << q << std::endl;
  Assert(qi != polynomials.end());
  size_t index = std::distance(polynomials.begin(), qi);
  Trace("neth") << "-> " << q << " (" << index << ")" << std::endl;
  currentReduction.steps.push_back(index);
}

void Tracer::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "reduction end: " << r << std::endl;
  std::string rr = ostring(r);
  if (d_parents.count(rr) == 0 && rr != d_reductionSeq.front())
  {
    Trace("ff::trace") << " keep" << std::endl;
    for (auto& s : d_reductionSeq)
    {
      addDep(s, rr);
    }
  }
  else
  {
    if (TraceIsOn("ff::trace"))
    {
      Trace("ff::trace") << " drop" << std::endl;
      if (d_parents.count(rr))
      {
        Trace("ff::trace") << " parents:";
        for (const auto& p : d_parents.at(rr))
        {
          Trace("ff::trace") << ", " << p;
        }
        Trace("ff::trace") << std::endl;
      }
    }
  }
  d_reductionSeq.clear();

  // Nethermind
  Trace("neth") << "reduction end: " << r << std::endl;

  auto ip = polynomials[currentReduction.initialPoly].p;
  if(currentReduction.steps.empty()) {
    if(r == ip) {
      currentReduction.finalPoly = currentReduction.initialPoly;
    } else if(r == ip / CoCoA::LC(ip)) {
      polynomials.push_back(Poly(Poly::Monic{}, r, ip));
      currentReduction.finalPoly = polynomials.size() - 1;
    } else {
      polynomials.push_back(Poly(Poly::Reduction{}, r, ip));
      currentReduction.finalPoly = polynomials.size() - 1;
    }
  } else {
    if (CoCoA::IsZero(r)) { 
      currentReduction.isFinalZeroPoly = true;
      currentReduction.finalPoly = 0;
    } else {
      if (CoCoA::deg(r) == 0) { currentReduction.isFinalZeroDegPoly = true; }
      polynomials.push_back(Poly(Poly::Reduction{}, r, ip));
      currentReduction.finalPoly = polynomials.size() - 1;
    } 
  }

  auto [it, inserted] = reductions.try_emplace(currentReduction.initialPoly, currentReduction);
  if(!inserted) { it->second = currentReduction; }
}

std::string Tracer::yesno(bool b) {
  if(b) { 
    return "yes"; 
  } else {
    return "no";
  }
}

void Tracer::addDep(const std::string& parent,
                               const std::string& child)
{
  d_parents[child].push_back(parent);
}

void Tracer::printReductions() {
  std::cout << "\tPOLYNOMIALS: " << std::endl;
  for(size_t i = 0; i < polynomials.size(); i += 1) {
    std::cout << i << ":\t" << polynomials[i].p;
    if(polynomials[i].spoly) {
      auto p = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f, polynomials[i].s1); });
      auto q = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f, polynomials[i].s2); });
      Assert(p != polynomials.end());
      Assert(q != polynomials.end());
      size_t index_p = std::distance(polynomials.begin(), p);
      size_t index_q = std::distance(polynomials.begin(), q);
      std::cout << " ; s(" << index_p << ", " << index_q << ")";
    } else if(polynomials[i].monic) {
      auto m = std::find_if(polynomials.begin(), polynomials.end(), [&](const Poly &f) { return equalPoly(f, polynomials[i].m); });
      Assert(m != polynomials.end());
      size_t index_m = std::distance(polynomials.begin(), m);
      std::cout << " ; m(" << index_m << ")";
    }
    std::cout << std::endl;
  }

  std::cout << "\tREDUCTIONS" << std::endl;
  for(size_t i = 1; i < polynomials.size(); i += 1) {
    const auto r = reductions.find(i); 
    //Trace("neth") << "POLY: " << i << std::endl;
    // Not all polynomials have reductions
    if(r != reductions.end()) {
      if(polynomials[r->second.initialPoly].spoly) {
        std::cout << r->second.initialPoly << "* -[";
      } else {
        std::cout << r->second.initialPoly << " -[";
      }
      for(const auto &s: r->second.steps) { 
        std::cout << s;
        if(&s != &r->second.steps.back()) { std::cout << " "; } 
      }
      std::cout << "]-> " << r->second.finalPoly << std::endl;
    }
  }
}

void Tracer::printRedUNSAT(Env& env, CocoaEncoder& enc) {
  const size_t finalPoly = polynomials.size() - 1;
  
  std::vector<size_t> pstack;
  std::unordered_map<size_t, bool> seen;
  
  pstack.push_back(finalPoly);
  seen[pstack[0]] = false;

  std::string tab = "";

  std::cout << tab << "UNSAT(" << std::endl; tab += "\t";
  std::cout << tab << "REDUCTIONS(" << std::endl; tab += "\t";
  while(!pstack.empty()) {
    const size_t next = pstack.back();
    //Trace("neth") << "NEXT(" << yesno(seen[next] || next <= p_input_size) << "): " << next << std::endl;
    
    if(seen[next]) { pstack.pop_back(); continue; }
    else if(next <= p_input_size) { seen[next] = true; pstack.pop_back(); continue; }

    seen[next] = true;
    const size_t offset = polynomials.size() - next;
    const Poly p = polynomials[next];
    
    if(p.monic) {
      // It is a moninc derivation, (backward) find polynomial that produced the monic
      const auto m = std::find_if(polynomials.rbegin() + offset, polynomials.rend(), [&](const Poly &f) { return equalPoly(f, p.m); });
      Assert(m != polynomials.rend());
      
      size_t monic_idx = polynomials.rend() - m - 1;
      std::cout << tab << "M(" << monic_idx << ", " << next << ")" << std::endl;
      pstack.push_back(monic_idx);
      
    } else if(p.spoly) {
      const auto s1 = std::find_if(polynomials.rbegin() + offset, polynomials.rend(), [&](const Poly &f) { return equalPoly(f, p.s1); });
      const auto s2 = std::find_if(polynomials.rbegin() + offset, polynomials.rend(), [&](const Poly &f) { return equalPoly(f, p.s2); });
      Assert(s1 != polynomials.rend()); 
      Assert(s2 != polynomials.rend());
      size_t s1_index = polynomials.rend() - s1 - 1;
      size_t s2_index = polynomials.rend() - s2 - 1;

      const auto o = CoCoA::owner(polynomials[s1_index].p);
      const auto s1i = CoCoA::BeginIter(polynomials[s1_index].p);
      const auto s2i = CoCoA::BeginIter(polynomials[s2_index].p);
      const auto ltp = CoCoA::monomial(o, CoCoA::PP(s1i));
      const auto ltq = CoCoA::monomial(o, CoCoA::PP(s2i));
      const auto lmp = CoCoA::coeff(s1i) * ltp;
      const auto lmq = CoCoA::coeff(s2i) * ltq;
      const auto lcm = CoCoA::lcm(ltp, ltq);
      // const auto spoly = ((lcm / lmp) * polynomials[s1_index].p) - ((lcm / lmq) * polynomials[s2_index].p);
      // std::cout << "SPOLY " << spoly << std::endl;

      //std::cout << "LCM: " << lcm << " LM: " << (lmp) << std::endl;
      std::cout << tab << "S(" << s1_index << "{" << (lcm / lmp) << "}, " << s2_index << "{" << (lcm / lmq) <<  "}, " << next;
      std::cout << ")" << std::endl;
      pstack.push_back(s1_index);
      pstack.push_back(s2_index);

    } else {
      const auto r = std::find_if(polynomials.rbegin() + offset, polynomials.rend(), [&](const Poly &f) { return equalPoly(f, p.r); });
      Assert(r != polynomials.rend());
      
      size_t r_index = polynomials.rend() - r - 1;
      const auto red = reductions.find(r_index);
      Assert(red != reductions.end());
      
      std::cout << tab << "R(" << red->second.initialPoly << "; ";
      pstack.push_back(r_index);

      CoCoA::RingElem pred = polynomials[red->second.initialPoly].p;
      CoCoA::RingElem left;

      for(const auto &s: red->second.steps) {
        const auto d = polynomials[s].p;

        CoCoA::RingElem c;
        while (true) {
          const auto pi = CoCoA::BeginIter(pred);
          const auto di = CoCoA::BeginIter(d);
          const auto lmp = CoCoA::coeff(pi) * CoCoA::monomial(CoCoA::owner(pred), CoCoA::PP(pi));
          const auto lmd = CoCoA::coeff(di) * CoCoA::monomial(CoCoA::owner(d), CoCoA::PP(di));

          if (CoCoA::IsDivisible(lmp, lmd)) {
            c = lmp / lmd;
            pred = pred - c * d;
            break;
          } else {
            left = left + lmp;
            pred = pred - lmp;
          }
        }
        
        std::cout << s << "{" << c << "}";
        if (&s != &red->second.steps.back()) { std::cout << ", "; }
        else { std::cout << "; "; } 
        pstack.push_back(s);
      }

      std::cout << red->second.finalPoly << ")" << std::endl;
    }
  }

  tab.pop_back();

  // REDUCTION
  std::cout << tab << ")" << std::endl;

  std::cout << tab << "POLYNOMIALS(" << std::endl; tab += "\t";
  std::map<Node, std::string> namedNodes = *env.d_namedNodes;

  for(size_t i = 0; i < polynomials.size(); i += 1) {
    if(!seen[i]) { continue; }
    for(const auto &nn : namedNodes) {
      if (enc.getTermEncoding(env.getRewriter()->rewrite(nn.first)) == polynomials[i].p) { 
        std::cout << tab << "PN(" << i << ", " << polynomials[i].p << ", " << nn.second << ")" << std::endl;
        goto found_name;
      }
    }
    std::cout << tab << "P(" << i << ", " << polynomials[i].p << ")" << std::endl;
    found_name:;
  }

  // POLYNOMIALS
  tab.pop_back();
  std::cout << tab << ")" << std::endl; 

  // UNSAT
  tab.pop_back();
  std::cout << tab << ")" << std::endl;  
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
