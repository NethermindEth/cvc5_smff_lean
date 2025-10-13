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

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__CORE_H
#define CVC5__THEORY__FF__CORE_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>

#include <functional>
#include <unordered_map>

#include "expr/node.h"
#include "theory/ff/cocoa_encoder.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * A dependency graph for CoCoA polynomials in Groebner basis computation.
 *
 * We represent polynomials as their strings.
 */
class Tracer
{
 public:
  /**
   * Create a tracer with these inputs.
   */
  Tracer(const std::vector<CoCoA::RingElem>& inputs);

  /**
   * Get the index of inputs responsible for this element.
   */
  std::vector<size_t> trace(const CoCoA::RingElem& i) const;

  /** CoCoA callback management */

  /**
   * Hook up to CoCoA callbacks. Don't move the object after calling this. Must
   * be called before CoCoA is used.
   */
  void setFunctionPointers();

  /**
   * Unhook from CoCoA callbacks. Should be called after you're done tracing.
   */
  void unsetFunctionPointers();

 private:
  /** CoCoA calls these functions */

  /** Call this when s = spoly(p, q); */
  void sPoly(CoCoA::ConstRefRingElem p,
             CoCoA::ConstRefRingElem q,
             CoCoA::ConstRefRingElem s);

  /** Tracing reduction p ->_q1 p1 ->_q2 p2 ->_q3 ... ->_qN -> r */

  /** Call this when we start reducing p. */
  void reductionStart(CoCoA::ConstRefRingElem p);
  /** Call this when there is a reduction on q. */
  void reductionStep(CoCoA::ConstRefRingElem q);
  /** Call this when we finish reducing with r. */
  void reductionEnd(CoCoA::ConstRefRingElem r);

  /** Internal helper functions */

  void addItem(const std::string&& item);
  void addDep(const std::string& parent, const std::string& child);

  /**
   * (key, vals) where key is known to be in the ideal when vals are.
   */
  std::unordered_map<std::string, std::vector<std::string>> d_parents{};
  /**
   * For each poly string, its index in the input sequence.
   */
  std::unordered_map<std::string, size_t> d_inputNumbers;

  /**
   * Sequence of dependencies for a reduction in progress.
   * See reductionStart, reductionStep, reductionEnd.
   */
  std::vector<std::string> d_reductionSeq{};

  /**
   * Handles to sPoly reductionStart, reductionStep, and reductionEnd that we
   * give to CoCoA.
   */
  std::function<void(CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem)>
      d_sPoly{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStep{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionEnd{};

 public:
  // Nethermind

  struct Poly {
    struct Monic final {};
    struct Reduction final {};

    CoCoA::RingElem p;

    // If the poly is a spoly, p1 and p2 holds its "parents"
    bool spoly;
    CoCoA::RingElem s1, s2;

    bool monic;
    CoCoA::RingElem m;

    bool reduction;
    CoCoA::RingElem r;

    Poly(CoCoA::RingElem pp) 
      : p(pp), spoly(false), monic(false), reduction(false) {} 
    Poly(Reduction, CoCoA::RingElem rr, CoCoA::RingElem pp) 
      : p(rr), spoly(false), monic(false), reduction(true), r(pp) {}
    Poly(Monic, CoCoA::RingElem mm, CoCoA::RingElem pp) 
      : p(mm), spoly(false), monic(true), m(pp), reduction(false) {} 
    Poly(CoCoA::RingElem pp, CoCoA::RingElem p1, CoCoA::RingElem p2)
      : p(pp), spoly(true), s1(p1), s2(p2), monic(false), reduction(false) {}

    bool operator==(const Poly &other) const { 
      return (p == other.p);
    }
  };

  struct Reduction {
    size_t initialPoly = 0;
    size_t finalPoly = -1;
    bool isFinalZeroPoly = false;
    bool isFinalZeroDegPoly = false;
    std::vector<size_t> steps;

    Reduction() {}
    Reduction(size_t i) : initialPoly(i) {}
    Reduction(const Reduction &other) {
      initialPoly = other.initialPoly;
      finalPoly = other.finalPoly;
      isFinalZeroPoly = other.isFinalZeroPoly;
      isFinalZeroDegPoly = other.isFinalZeroDegPoly;
      steps = other.steps;
    }

    Reduction& operator=(const Reduction &other) {
      if (this != &other) {
        initialPoly = other.initialPoly;
        finalPoly = other.finalPoly;
        isFinalZeroPoly = other.isFinalZeroPoly;
        isFinalZeroDegPoly = other.isFinalZeroDegPoly;
        steps = other.steps;
      }

      return *this;
    }
  };

  // struct PolyReduction {
  //   bool zeroPoly = false;
  //   bool zeroDegPoly = false;
  //   std::string zeroDegPolyStr = "";
  //   size_t initialPoly;
  //   size_t finalPoly;
  //   std::vector<size_t> steps;
  // };
  
  size_t p_input_size = 0;
  CoCoA::RingElem ZERO;
  std::vector<Poly> polynomials{};
  // Table from Polynomial (RingElem) to its index in polynomials.
  //std::unordered_map<CoCoA::RingElem, size_t> polyIndex{};
  // Associate initial polynomial index with its reduction
  std::unordered_map<size_t, Reduction> reductions{};

  // Store current reduction
  Reduction currentReduction;

  void printReductions();
  void printRedUNSAT(Env& env, CocoaEncoder& enc);
  std::string yesno(bool b);

  bool equalPoly(const Poly &f, const CoCoA::RingElem &q) {
    if(CoCoA::IsZero(f.p)) { return false; }
    else { return f.p == q; }
  }
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__CORE_H */

#endif /* CVC5_USE_COCOA */
