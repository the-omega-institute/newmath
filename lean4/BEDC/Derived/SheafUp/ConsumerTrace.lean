import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_append_no_zero_extension
    {root row tail : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      List.Mem row (left ++ right) -> hsame row (BHist.e0 tail) -> False := by
  intro leftTrace rightTrace rowMem sameRow
  have appended :
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right) :=
    SheafConsumerAccessTrace_append_closed leftTrace rightTrace
  have rowUnary : UnaryHistory row :=
    appended.right.right row rowMem
  exact unary_no_zero_extension (unary_transport rowUnary sameRow)

theorem SheafSchemeChartGluingTrace_result_deterministic
    {point common : BHist} {sections : List BHist} {outA outB : BHist} :
    SheafSchemeChartGluingTrace point common sections outA ->
      SheafSchemeChartGluingTrace point common sections outB ->
        UnaryHistory outA ∧ UnaryHistory outB ∧ hsame outA outB := by
  intro traceA
  induction traceA generalizing outB with
  | nil pointUnary commonUnary =>
      intro traceB
      cases traceB with
      | nil _ _ =>
          exact And.intro unary_empty (And.intro unary_empty (hsame_refl BHist.Empty))
  | cons commonUnary sectionUnary commonSection tailTrace germTail ih =>
      intro traceB
      cases traceB with
      | cons commonUnaryB sectionUnaryB commonSectionB tailTraceB germTailB =>
          have tailRows := ih tailTraceB
          have sameGerm :=
            cont_deterministic commonSection commonSectionB
          have sameOut :=
            cont_respects_hsame sameGerm tailRows.right.right germTail germTailB
          have outUnary :=
            unary_cont_closed
              (unary_cont_closed commonUnary sectionUnary commonSection)
              tailRows.left germTail
          have outUnaryB :=
            unary_cont_closed
              (unary_cont_closed commonUnaryB sectionUnaryB commonSectionB)
              tailRows.right.left germTailB
          exact And.intro outUnary (And.intro outUnaryB sameOut)

end BEDC.Derived.SheafUp
