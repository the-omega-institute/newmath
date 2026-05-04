import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_unit_result_factors_unit {d q : BHist} :
    NatMul d q (BHist.e1 BHist.Empty) ->
      hsame d (BHist.e1 BHist.Empty) /\ hsame q (BHist.e1 BHist.Empty) := by
  intro mul
  cases mul with
  | succ previous step =>
      have stepCases := cont_e1_result_inversion step
      cases stepCases with
      | inl emptyFactor =>
          cases emptyFactor with
          | intro dEmpty previousUnit =>
              cases dEmpty
              have previousEmpty : hsame _ BHist.Empty :=
                NatMul_empty_left_result_empty previous
              have unitEmpty : hsame (BHist.e1 BHist.Empty) BHist.Empty :=
                hsame_trans (hsame_symm previousUnit) previousEmpty
              exact False.elim (not_hsame_e1_empty unitEmpty)
      | inr visibleFactor =>
          cases visibleFactor with
          | intro dTail data =>
              cases data with
              | intro dEq tailCont =>
                  cases dEq
                  have emptyParts := cont_empty_result_inversion tailCont
                  cases emptyParts.left
                  cases emptyParts.right
                  have qTailEmpty : hsame _ BHist.Empty :=
                    (NatMul_nonempty_multiplicand_empty_result_iff
                      (unary_e1_closed unary_empty) not_hsame_e1_empty).mp previous
                  cases qTailEmpty
                  exact And.intro (hsame_refl (BHist.e1 BHist.Empty))
                    (hsame_refl (BHist.e1 BHist.Empty))

end BEDC.Derived.PrimeUp
