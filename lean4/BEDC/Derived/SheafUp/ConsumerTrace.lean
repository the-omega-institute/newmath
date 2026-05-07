import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafConsumerTraceCompositionSource (root : BHist) (left right : List BHist) : Prop :=
  SheafConsumerAccessTrace root left ∧
    SheafConsumerAccessTrace root right ∧
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right)

theorem SheafConsumerTraceCompositionSource_closed
    {root : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      SheafConsumerTraceCompositionSource root left right := by
  intro leftTrace rightTrace
  have appended :
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right) :=
    SheafConsumerAccessTrace_append_closed leftTrace rightTrace
  exact And.intro leftTrace
    (And.intro rightTrace (And.intro appended.left appended.right))

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

theorem SheafConsumerAccessTraceCompositionSource_membership_split
    {root row : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      List.Mem row (left ++ right) ->
        (List.Mem row left ∧ UnaryHistory row) ∨
          (List.Mem row right ∧ UnaryHistory row) := by
  intro leftTrace rightTrace rowMem
  induction left with
  | nil =>
      exact Or.inr (And.intro rowMem (rightTrace.right row rowMem))
  | cons head tail ih =>
      cases rowMem with
      | head =>
          exact Or.inl
            (And.intro (List.Mem.head tail) (leftTrace.right row (List.Mem.head tail)))
      | tail head tailMem =>
          have tailTrace : SheafConsumerAccessTrace root tail :=
            And.intro leftTrace.left
              (by
                intro row rowMem
                exact leftTrace.right row (List.Mem.tail head rowMem))
          have splitTail := ih tailTrace tailMem
          cases splitTail with
          | inl leftRow =>
              exact Or.inl
                (And.intro (List.Mem.tail head leftRow.left) leftRow.right)
          | inr rightRow =>
              exact Or.inr rightRow

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
