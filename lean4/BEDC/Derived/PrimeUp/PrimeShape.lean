import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem NatPrime_successor_tail_nonempty {p : BHist} :
    NatPrime p -> ∃ tail : BHist, hsame p (BHist.e1 tail) ∧ UnaryHistory tail ∧
      (hsame tail BHist.Empty -> False) := by
  intro prime
  cases p with
  | Empty =>
      exact False.elim (NatUnaryStrictPrefix_empty_right_absurd prime.right.left)
  | e0 tail =>
      cases prime.left
  | e1 tail =>
      exact ⟨tail, hsame_refl (BHist.e1 tail), unary_e1_inversion prime.left,
        fun tailEmpty => by
          cases tailEmpty
          exact NatPrime_unit_absurd prime⟩

theorem NatPrime_divisor_positive_shape {p d : BHist} :
    NatPrime p -> NatDivides d p ->
      ∃ tail : BHist, hsame d (BHist.e1 tail) ∧ UnaryHistory tail := by
  intro prime divides
  have dCarrier : UnaryHistory d := by
    cases divides with
    | intro _ qData =>
        exact NatMul_left_unary qData.right
  cases d with
  | Empty =>
      exact False.elim
        (NatPrime_divisor_empty_absurd prime divides (hsame_refl BHist.Empty))
  | e0 tail =>
      cases dCarrier
  | e1 tail =>
      exact ⟨tail, hsame_refl (BHist.e1 tail), unary_e1_inversion dCarrier⟩

end BEDC.Derived.PrimeUp
