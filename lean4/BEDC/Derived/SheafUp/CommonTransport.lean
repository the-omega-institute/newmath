import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafBHistPointGermComparison_common_transport
    {point openA openB sectA sectB germA germB common common' germA' germB' : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      hsame common common' -> Cont common' sectA germA' -> Cont common' sectB germB' ->
        SheafBHistPointGermComparison point openA sectA germA' openB sectB germB' common' ∧
          hsame germA germA' ∧ hsame germB germB' := by
  intro comparison sameCommon rowA rowB
  have commonUnary : UnaryHistory common' :=
    unary_transport comparison.right.right.right.left sameCommon
  have sameOpenA : hsame common' openA :=
    hsame_trans (hsame_symm sameCommon) comparison.right.right.right.right.left
  have sameOpenB : hsame common' openB :=
    hsame_trans (hsame_symm sameCommon) comparison.right.right.right.right.right.left
  have sameGermA : hsame germA germA' :=
    cont_respects_hsame sameCommon (hsame_refl sectA)
      comparison.right.right.right.right.right.right.left rowA
  have sameGermB : hsame germB germB' :=
    cont_respects_hsame sameCommon (hsame_refl sectB)
      comparison.right.right.right.right.right.right.right.left rowB
  have sameTransportedGerms : hsame germA' germB' :=
    hsame_trans (hsame_symm sameGermA)
      (hsame_trans comparison.right.right.right.right.right.right.right.right sameGermB)
  exact And.intro
    (And.intro comparison.left
      (And.intro comparison.right.left
        (And.intro comparison.right.right.left
          (And.intro commonUnary
            (And.intro sameOpenA
              (And.intro sameOpenB
                (And.intro rowA
                  (And.intro rowB sameTransportedGerms))))))))
    (And.intro sameGermA sameGermB)

end BEDC.Derived.SheafUp
