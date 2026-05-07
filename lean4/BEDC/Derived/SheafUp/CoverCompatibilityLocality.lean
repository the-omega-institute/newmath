import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafIndexedCoverCompatibilityLocality
    (point openA openB sectA sectB germA germB common : BHist) : Prop :=
  SheafBHistPointGermLedger point openA sectA germA ∧
    SheafBHistPointGermLedger point openB sectB germB ∧ UnaryHistory common ∧
      hsame common openA ∧ hsame common openB ∧ Cont common sectA germA ∧
        Cont common sectB germB ∧ hsame germA germB

theorem SheafIndexedCoverCompatibilityLocality_common_refinement
    {point openA openB sectA sectB germA germB common : BHist} :
    SheafIndexedCoverCompatibilityLocality point openA openB sectA sectB germA germB common ->
      SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ∧
        SheafBHistPointGermLedger point common sectA germA ∧
          SheafBHistPointGermLedger point common sectB germB := by
  intro locality
  have pointUnary : UnaryHistory point := locality.left.left
  have openAUnary : UnaryHistory openA := locality.left.right.left
  have openBUnary : UnaryHistory openB := locality.right.left.right.left
  have commonUnary : UnaryHistory common := locality.right.right.left
  have commonOpenA : hsame common openA := locality.right.right.right.left
  have commonOpenB : hsame common openB := locality.right.right.right.right.left
  have commonSectA : Cont common sectA germA := locality.right.right.right.right.right.left
  have commonSectB : Cont common sectB germB := locality.right.right.right.right.right.right.left
  have sameGerm : hsame germA germB := locality.right.right.right.right.right.right.right
  have comparison :
      SheafBHistPointGermComparison point openA sectA germA openB sectB germB common :=
    And.intro pointUnary
      (And.intro openAUnary
        (And.intro openBUnary
          (And.intro commonUnary
            (And.intro commonOpenA
              (And.intro commonOpenB
                (And.intro commonSectA
                  (And.intro commonSectB sameGerm)))))))
  have ledgerA : SheafBHistPointGermLedger point common sectA germA :=
    And.intro pointUnary (And.intro commonUnary commonSectA)
  have ledgerB : SheafBHistPointGermLedger point common sectB germB :=
    And.intro pointUnary (And.intro commonUnary commonSectB)
  exact And.intro
    comparison
    (And.intro ledgerA ledgerB)

end BEDC.Derived.SheafUp
