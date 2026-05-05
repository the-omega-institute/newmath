import BEDC.Derived.PrimeUp.ResultBoundary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem NatPrime_NatMul_factor_unit_or_prime {p d q : BHist} :
    NatPrime p -> UnaryHistory d -> UnaryHistory q -> NatMul d q p ->
      (hsame d (BHist.e1 BHist.Empty) ∧ hsame q p) ∨
        (hsame d p ∧ hsame q (BHist.e1 BHist.Empty)) := by
  intro prime dUnary qUnary mul
  have divides : NatDivides d p :=
    Exists.intro q (And.intro qUnary mul)
  have divisorCases := prime.right.right d dUnary divides
  cases divisorCases with
  | inl dUnit =>
      cases dUnit
      exact Or.inl
        (And.intro (hsame_refl (BHist.e1 BHist.Empty))
          (hsame_symm (NatMul_unit_left_hsame qUnary mul)))
  | inr dPrime =>
      have dNonunit : hsame d (BHist.e1 BHist.Empty) -> False := by
        intro dUnit
        cases dUnit
        cases dPrime
        exact NatPrime_unit_absurd prime
      exact Or.inr
        (NatPrime_NatMul_nonunit_factor_multiplier_unit prime dUnary qUnary mul dNonunit)

end BEDC.Derived.PrimeUp
