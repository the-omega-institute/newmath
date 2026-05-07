import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafCoverPresentationClassifier_symmetric
    {point openA openB sectA sectB germA germB common : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      UnaryHistory point ∧ UnaryHistory openB ∧ UnaryHistory openA ∧ UnaryHistory common ∧
        hsame common openB ∧ hsame common openA ∧ Cont common sectB germB ∧
          Cont common sectA germA ∧ hsame germB germA ∧
            SheafBHistPointGermComparison point openB sectB germB openA sectA germA common := by
  intro comparison
  have reversed :
      SheafBHistPointGermComparison point openB sectB germB openA sectA germA common :=
    And.intro comparison.left
      (And.intro comparison.right.right.left
        (And.intro comparison.right.left
          (And.intro comparison.right.right.right.left
            (And.intro comparison.right.right.right.right.right.left
              (And.intro comparison.right.right.right.right.left
                (And.intro comparison.right.right.right.right.right.right.right.left
                  (And.intro comparison.right.right.right.right.right.right.left
                    (hsame_symm comparison.right.right.right.right.right.right.right.right))))))))
  exact And.intro comparison.left
    (And.intro comparison.right.right.left
      (And.intro comparison.right.left
        (And.intro comparison.right.right.right.left
          (And.intro comparison.right.right.right.right.right.left
            (And.intro comparison.right.right.right.right.left
              (And.intro comparison.right.right.right.right.right.right.right.left
                (And.intro comparison.right.right.right.right.right.right.left
                  (And.intro
                    (hsame_symm comparison.right.right.right.right.right.right.right.right)
                    reversed))))))))

end BEDC.Derived.SheafUp
