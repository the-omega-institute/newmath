import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryClassifier_right_hsame_inversion {Left Right : BHist -> Prop}
    {l r : BHist} :
    SumHistoryClassifier Left Right hsame hsame (BHist.e1 l) (BHist.e1 r) -> hsame l r := by
  intro classifier
  cases classifier with
  | inl leftData =>
      cases leftData with
      | intro left0 rest =>
          cases rest with
          | intro _ data =>
              exact False.elim (not_hsame_e1_e0 data.left)
  | inr rightData =>
      cases rightData with
      | intro right0 rest =>
          cases rest with
          | intro right1 data =>
              exact hsame_trans (hsame_trans (hsame_e1_iff.mp data.left) data.right.right)
                (hsame_symm (hsame_e1_iff.mp data.right.left))

end BEDC.Derived.SumUp
