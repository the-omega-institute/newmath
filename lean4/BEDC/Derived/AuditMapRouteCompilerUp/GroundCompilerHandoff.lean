import BEDC.Derived.AuditMapRouteCompilerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapRouteCompilerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem AuditMapRouteCompilerCarrier_groundcompiler_handoff
    {event source recognizer gate theoremCode chapterCode metric cannotClaim ledger transport
      continuation provenance name routeRead handoffRead : BHist} :
    Cont event source routeRead ->
      Cont routeRead ledger handoffRead ->
        UnaryHistory event ->
          UnaryHistory source ->
            UnaryHistory ledger ->
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row event ∨ hsame row source ∨ hsame row ledger ∨
                      hsame row routeRead ∨ hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont event source routeRead ∧
                      Cont routeRead ledger handoffRead)
                  hsame ∧
                UnaryHistory routeRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro eventSourceRoute routeLedgerHandoff eventUnary sourceUnary ledgerUnary
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed eventUnary sourceUnary eventSourceRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed routeUnary ledgerUnary routeLedgerHandoff
  have sourceHandoff : hsame handoffRead handoffRead ∧ UnaryHistory handoffRead :=
    ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row event ∨ hsame row source ∨ hsame row ledger ∨ hsame row routeRead ∨
            hsame row handoffRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont event source routeRead ∧ Cont routeRead ledger handoffRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row col sameRowCol
        exact hsame_symm sameRowCol
      equiv_trans := by
        intro row col out sameRowCol sameColOut
        exact hsame_trans sameRowCol sameColOut
      carrier_respects_equiv := by
        intro row col sameRowCol sourceRow
        cases sameRowCol
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨handoffUnary, eventSourceRoute, routeLedgerHandoff⟩
  }
  exact ⟨cert, routeUnary, handoffUnary⟩

end BEDC.Derived.AuditMapRouteCompilerUp
