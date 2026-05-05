import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem TrialDiv_bound_unit_or_successor_shape {b n : BHist} :
    TrialDiv b n ->
      hsame b (BHist.e1 BHist.Empty) ∨
        (∃ t : BHist, hsame b (BHist.e1 (BHist.e1 t)) ∧ UnaryHistory t) := by
  intro trial
  have shape := TrialDiv_bound_positive_shape trial
  cases shape with
  | intro tail data =>
      cases tail with
      | Empty =>
          exact Or.inl data.left
      | e0 tail =>
          exact False.elim (unary_no_zero_extension data.right)
      | e1 tail =>
          exact Or.inr
            (Exists.intro tail (And.intro data.left (unary_e1_inversion data.right)))

theorem TrialDiv_bound_unit_strict_prefix_after_cont {b n b' : BHist} :
    TrialDiv b n -> Cont b (BHist.e1 BHist.Empty) b' ->
      BEDC.Derived.NatUp.NatUnaryStrictPrefix (BHist.e1 BHist.Empty) b' := by
  intro trial stepCont
  have stepStrict : NatUnaryStrictPrefix b b' :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, (fun empty => by cases empty),
      stepCont⟩
  cases TrialDiv_bound_unit_prefix_or_self trial with
  | inl previousStrict =>
      cases NatUnaryStrictPrefix_trans_composite_tail previousStrict stepStrict with
      | intro _ composite =>
          exact composite.right.right.right
  | inr sameUnit =>
      exact NatUnaryStrictPrefix_cont_hsame_transport (unary_e1_closed unary_empty)
        (fun empty => by cases empty) stepCont sameUnit (hsame_refl _)

theorem TrialDiv_target_unary_and_bound_trichotomy {b n : BHist} :
    TrialDiv b n ->
      UnaryHistory n ∧
        (hsame b n ∨ NatUnaryStrictPrefix b n ∨ NatUnaryStrictPrefix n b) := by
  intro trial
  have boundUnary : UnaryHistory b := TrialDiv_bound_unary trial
  have targetUnary : UnaryHistory n := by
    induction trial with
    | unit hn =>
        exact hn
    | step previous _screen _stepCont ih =>
        exact ih (TrialDiv_bound_unary previous)
  exact And.intro targetUnary
    (NatUnaryPrefix_trichotomy_hsame_strict boundUnary targetUnary)

end BEDC.Derived.PrimeUp
