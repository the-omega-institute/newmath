import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafSchemeGluingCoverRow_chart_trace_cons_readback
    {point common sectionHist out : BHist} {sections : List BHist} :
    SheafSchemeChartGluingTrace point common (sectionHist :: sections) out ->
      ∃ germ : BHist, ∃ tailOut : BHist,
        UnaryHistory common ∧ UnaryHistory sectionHist ∧ Cont common sectionHist germ ∧
          SheafSchemeChartGluingTrace point common sections tailOut ∧ Cont germ tailOut out ∧
            UnaryHistory germ ∧ UnaryHistory out := by
  intro trace
  cases trace with
  | cons commonUnary sectionUnary commonSection tailTrace germTail =>
      have germUnary : UnaryHistory _ :=
        unary_cont_closed commonUnary sectionUnary commonSection
      have tailUnary : UnaryHistory _ :=
        SheafSchemeChartGluingTrace_unary_result tailTrace
      have outUnary : UnaryHistory out :=
        unary_cont_closed germUnary tailUnary germTail
      exact ⟨_, _, commonUnary, sectionUnary, commonSection, tailTrace, germTail, germUnary,
        outUnary⟩

end BEDC.Derived.SheafUp
