import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
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

theorem NatPrime_empty_absurd {p : BHist} :
    NatPrime p -> hsame p BHist.Empty -> False := by
  intro prime sameEmpty
  cases sameEmpty
  exact NatUnaryStrictPrefix_empty_right_absurd prime.right.left

theorem NatPrime_NatDivides_strict_between_absurd {p d : BHist} :
    NatPrime p -> UnaryHistory d -> NatDivides d p ->
      NatUnaryStrictPrefix (BHist.e1 BHist.Empty) d -> NatUnaryStrictPrefix d p -> False := by
  intro prime dUnary divides unitStrict primeStrict
  have divisorBoundary := prime.right.right d dUnary divides
  cases divisorBoundary with
  | inl dUnit =>
      cases unitStrict with
      | intro tail data =>
          exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
            data.left data.right.left data.right.right (hsame_symm dUnit)
  | inr dPrime =>
      cases primeStrict with
      | intro tail data =>
          exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
            data.left data.right.left data.right.right dPrime

theorem NatPrime_hsame_transport {p p' : BHist} :
    NatPrime p -> hsame p p' -> UnaryHistory p' ∧ NatPrime p' := by
  intro prime sameP
  have pUnary' : UnaryHistory p' := unary_transport prime.left sameP
  have strictUnit' : NatUnaryStrictPrefix (BHist.e1 BHist.Empty) p' := by
    cases prime.right.left with
    | intro tail data =>
        exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left data.right.right
          (hsame_refl (BHist.e1 BHist.Empty)) sameP
  have divisorClassifier' :
      ∀ d : BHist, UnaryHistory d -> NatDivides d p' ->
        hsame d (BHist.e1 BHist.Empty) ∨ hsame d p' := by
    intro d dUnary dividesTarget
    have dividesSource : NatDivides d p :=
      (NatDivides_endpoint_hsame_transport dividesTarget (hsame_refl d) (hsame_symm sameP)).right.right
    cases prime.right.right d dUnary dividesSource with
    | inl dUnit =>
        exact Or.inl dUnit
    | inr dSameP =>
        exact Or.inr (hsame_trans dSameP sameP)
  exact And.intro pUnary' (And.intro pUnary' (And.intro strictUnit' divisorClassifier'))

theorem PrimeStabilityCert_fields :
    (forall {p p' : BHist}, NatPrime p -> hsame p p' -> UnaryHistory p' ∧ NatPrime p') ∧
      (forall {d d' n n' : BHist}, NatDivides d n -> hsame d d' -> hsame n n' ->
        UnaryHistory d' ∧ UnaryHistory n' ∧ NatDivides d' n') := by
  constructor
  · intro p p' prime sameP
    exact NatPrime_hsame_transport prime sameP
  · intro d d' n n' divides sameD sameN
    exact NatDivides_endpoint_hsame_transport divides sameD sameN

end BEDC.Derived.PrimeUp
