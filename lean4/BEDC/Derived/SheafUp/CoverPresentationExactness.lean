import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafCoverPresentation_common_refinement_global_comparison
    {point common openA openB sectionA sectionB germA germB globalA globalB : BHist} :
    UnaryHistory point -> UnaryHistory common -> hsame common openA -> hsame common openB ->
      Cont common sectionA germA -> Cont common sectionB germB -> hsame germA germB ->
        Cont common sectionA globalA -> Cont common sectionB globalB -> hsame germA globalA ->
          hsame germB globalB ->
            SheafBHistPointGermComparison point openA sectionA globalA openB sectionB globalB
                common ∧
              hsame globalA globalB := by
  intro pointUnary commonUnary sameOpenA sameOpenB _germACont _germBCont sameGerm
    globalACont globalBCont sameGlobalA sameGlobalB
  have openAUnary : UnaryHistory openA :=
    unary_transport commonUnary sameOpenA
  have openBUnary : UnaryHistory openB :=
    unary_transport commonUnary sameOpenB
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA) (hsame_trans sameGerm sameGlobalB)
  exact And.intro
    (And.intro pointUnary
      (And.intro openAUnary
        (And.intro openBUnary
          (And.intro commonUnary
            (And.intro sameOpenA
              (And.intro sameOpenB
                (And.intro globalACont
                  (And.intro globalBCont sameGlobal))))))))
    sameGlobal

end BEDC.Derived.SheafUp
