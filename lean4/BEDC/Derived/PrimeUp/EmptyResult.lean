import BEDC.Derived.PrimeUp.EmptyRight

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatMul_succ_result_empty_left_empty_iff {d q n : BHist} :
    NatMul d (BHist.e1 q) n -> (hsame n BHist.Empty ↔ hsame d BHist.Empty) := by
  intro mul
  constructor
  · intro resultEmpty
    exact NatMul_succ_result_empty_left_empty mul resultEmpty
  · intro dEmpty
    cases dEmpty
    exact NatMul_empty_left_result_empty mul

theorem NatDivides_empty_left_iff {n : BHist} :
    NatDivides BHist.Empty n ↔ hsame n BHist.Empty := by
  constructor
  · intro divides
    exact NatDivides_empty_left_result_empty divides
  · intro nEmpty
    cases nEmpty
    exact (NatDivides_empty_right_iff (d := BHist.Empty)).mpr unary_empty

theorem NatMul_empty_result_iff_factor_empty_or_multiplier_empty {d q n : BHist} :
    NatMul d q n -> (hsame n BHist.Empty ↔ hsame d BHist.Empty ∨ hsame q BHist.Empty) := by
  intro mul
  constructor
  · intro resultEmpty
    cases resultEmpty
    exact NatMul_empty_result_factor_empty_or_multiplier_empty mul
  · intro emptyFactor
    cases emptyFactor with
    | inl dEmpty =>
        cases dEmpty
        exact NatMul_empty_left_result_empty mul
    | inr qEmpty =>
        cases qEmpty
        have emptyProduct : NatMul d BHist.Empty BHist.Empty :=
          (NatMul_empty_right_iff (d := d) (n := BHist.Empty)).mpr
            ⟨NatMul_left_unary mul, hsame_refl BHist.Empty⟩
        exact NatMul_functional (NatMul_left_unary mul) mul emptyProduct

theorem NatMul_empty_left_iff {q n : BHist} :
    NatMul BHist.Empty q n ↔ UnaryHistory q ∧ hsame n BHist.Empty := by
  constructor
  · intro mul
    exact And.intro (NatMul_right_unary mul) (NatMul_empty_left_result_empty mul)
  · intro data
    cases data with
    | intro qUnary resultEmpty =>
        cases resultEmpty
        induction q with
        | Empty =>
            exact NatMul.zero unary_empty
        | e0 q =>
            cases qUnary
        | e1 q ih =>
            exact NatMul.succ (ih qUnary) (BEDC.FKernel.Cont.cont_intro rfl)

end BEDC.Derived.PrimeUp
