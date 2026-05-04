import BEDC.Derived.NatTransUp
import BEDC.Derived.CategoryUp.CompResultNonemptySourceTargetCases

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_target_visible
    {p q r a eta theta k : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        ∃ s : BHist, append r a = BHist.e1 s ∧ UnaryHistory k ∧ UnaryHistory s ∧
          Cont (append p a) (BHist.e1 k) (BHist.e1 s) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases
      left.right.right.right right.right.right.right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro s data =>
              cases data.left
              exact Exists.intro s data.right
  | inr visibleSource =>
      cases visibleSource with
      | intro sourceTail sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro s data =>
                  cases data.right.left
                  have sourceSame : hsame (BHist.e1 sourceTail) (append p a) := by
                    exact data.left.symm
                  have sourceRel : Cont (append p a) (BHist.e1 k) (BHist.e1 s) :=
                    cont_hsame_transport sourceSame (hsame_refl (BHist.e1 k))
                      (hsame_refl (BHist.e1 s)) data.right.right.right.right.right.right
                  exact Exists.intro s
                    (And.intro data.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left sourceRel)))

end BEDC.Derived.NatTransUp
