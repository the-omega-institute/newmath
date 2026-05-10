import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafSchemeChartGluingTrace_cons_readback
    {point common sectionHist out : BHist} {rest : List BHist} :
    SheafSchemeChartGluingTrace point common (sectionHist :: rest) out ->
      UnaryHistory common ∧ UnaryHistory sectionHist ∧
        exists germ : BHist, exists tailOut : BHist,
          UnaryHistory germ ∧ Cont common sectionHist germ ∧
            SheafSchemeChartGluingTrace point common rest tailOut ∧ Cont germ tailOut out := by
  intro trace
  cases trace with
  | cons commonUnary sectionUnary commonSection tailTrace germTail =>
      have germUnary : UnaryHistory _ :=
        unary_cont_closed commonUnary sectionUnary commonSection
      exact And.intro commonUnary
        (And.intro sectionUnary
          (Exists.intro _
            (Exists.intro _
              (And.intro germUnary
                (And.intro commonSection (And.intro tailTrace germTail))))))

end BEDC.Derived.SheafUp
