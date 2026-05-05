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

theorem NatPrime_strict_unit_successor_shape {p : BHist} :
    NatPrime p -> ∃ tail : BHist, hsame p (BHist.e1 (BHist.e1 tail)) ∧
      UnaryHistory tail := by
  intro prime
  have successor := NatPrime_successor_tail_nonempty prime
  cases successor with
  | intro firstTail firstData =>
      have strictTail := unary_history_nonempty_e1_tail firstData.2.1 firstData.2.2
      cases strictTail with
      | intro tail tailData =>
          cases tailData.1
          exact ⟨tail, firstData.1, tailData.2⟩

end BEDC.Derived.PrimeUp
