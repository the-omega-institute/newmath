import BEDC.Derived.AuditMapRouteCompilerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapRouteCompilerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

theorem AuditMapRouteCompilerNonescape
    {E S G A T C M F L H K P N eventGate theoremChapter auditLedger
      consumerRead : BHist} :
    Cont E G eventGate ->
      Cont T C theoremChapter ->
        Cont eventGate theoremChapter auditLedger ->
          Cont auditLedger K consumerRead ->
            UnaryHistory E ->
              UnaryHistory G ->
                UnaryHistory T ->
                  UnaryHistory C ->
                    UnaryHistory K ->
                      auditMapRouteCompilerToEventFlow
                            (AuditMapRouteCompilerUp.mk E S G A T C M F L H K P N) =
                          [[BMark.b0],
                            auditMapRouteCompilerEncodeBHist E,
                            [BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist S,
                            [BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist G,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist A,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist T,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist C,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b0],
                            auditMapRouteCompilerEncodeBHist M,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist F,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist L,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist H,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist K,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
                            auditMapRouteCompilerEncodeBHist P,
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                              BMark.b0],
                            auditMapRouteCompilerEncodeBHist N] ∧
                        UnaryHistory eventGate ∧ UnaryHistory theoremChapter ∧
                          UnaryHistory auditLedger ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro eventRoute theoremRoute auditRoute consumerRoute eventUnary recognizerUnary theoremUnary
    chapterUnary continuationUnary
  have eventGateUnary : UnaryHistory eventGate :=
    unary_cont_closed eventUnary recognizerUnary eventRoute
  have theoremChapterUnary : UnaryHistory theoremChapter :=
    unary_cont_closed theoremUnary chapterUnary theoremRoute
  have auditLedgerUnary : UnaryHistory auditLedger :=
    unary_cont_closed eventGateUnary theoremChapterUnary auditRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditLedgerUnary continuationUnary consumerRoute
  exact ⟨rfl, eventGateUnary, theoremChapterUnary, auditLedgerUnary, consumerReadUnary⟩

end BEDC.Derived.AuditMapRouteCompilerUp
