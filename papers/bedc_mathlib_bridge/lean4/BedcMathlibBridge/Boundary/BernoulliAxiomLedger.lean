import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Bernoulli axiom ledger

This module is audit-only boundary data. It records the axiom footprint of the
mathlib Bernoulli number, Bernoulli polynomial, and Faulhaber surfaces consumed
by the targeted BEDC Bernoulli cluster comparison. It exports no
BEDC-to-mathlib bridge theorem.
-/

namespace BedcMathlibBridge.Boundary.BernoulliAxiomLedger

open scoped BigOperators

noncomputable section

def auditBernoulliNumber : Nat -> Rat :=
  bernoulli

def auditPositiveBernoulliNumber : Nat -> Rat :=
  bernoulli'

def auditBernoulliPolynomial : Nat -> Polynomial Rat :=
  Polynomial.bernoulli

def auditBernoulliSmallValueTheorems : Prop :=
  bernoulli 0 = 1 ∧ bernoulli 1 = -1 / 2 ∧ bernoulli 2 = 6⁻¹ ∧ bernoulli' 4 = -1 / 30

def auditBernoulliPolynomialLaws : Prop :=
  (∀ n : Nat, Polynomial.eval 0 (Polynomial.bernoulli n) = bernoulli n) ∧
    (∀ n : Nat,
      Polynomial.derivative (Polynomial.bernoulli n) =
        Polynomial.C (n : Rat) * Polynomial.bernoulli (n - 1))

def auditFaulhaberBernoulliFormula : Prop :=
  ∀ n p : Nat,
    ∑ k ∈ Finset.range n, (k : Rat) ^ p =
      ∑ i ∈ Finset.range (p + 1),
        bernoulli i * ((p + 1).choose i : Rat) * (n : Rat) ^ (p + 1 - i) / ((p : Rat) + 1)

def auditFaulhaberBernoulliPolynomialFormula : Prop :=
  ∀ n p : Nat,
    ((p : Rat) + 1) * ∑ k ∈ Finset.range n, (k : Rat) ^ p =
      Polynomial.eval (n : Rat) (Polynomial.bernoulli p.succ) - bernoulli p.succ

#print axioms auditBernoulliNumber
#print axioms auditPositiveBernoulliNumber
#print axioms auditBernoulliPolynomial
#print axioms auditBernoulliSmallValueTheorems
#print axioms auditBernoulliPolynomialLaws
#print axioms auditFaulhaberBernoulliFormula
#print axioms auditFaulhaberBernoulliPolynomialFormula

#check bernoulli
#check bernoulli'
#check Polynomial.bernoulli
#check sum_range_pow
#check Polynomial.sum_range_pow_eq_bernoulli_sub

end

end BedcMathlibBridge.Boundary.BernoulliAxiomLedger
