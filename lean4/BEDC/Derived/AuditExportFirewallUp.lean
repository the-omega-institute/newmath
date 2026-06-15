import BEDC.Derived.AuditExportFirewallUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditExportFirewallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem AuditExportFirewallCarrier_nonescape
    {claim positive audit failure registry consistency ledger transport replay provenance name
      conflictRead : BHist} :
    Cont positive failure conflictRead →
      UnaryHistory positive →
        UnaryHistory failure →
          auditExportFirewallFields
              (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                transport replay provenance name) =
            [claim, positive, audit, failure, registry, consistency, ledger, transport, replay,
              provenance, name] →
            UnaryHistory conflictRead ∧
              List.Mem positive
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) ∧
              List.Mem failure
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) ∧
              List.Mem ledger
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro conflictRoute positiveUnary failureUnary fieldsExact
  constructor
  · exact unary_cont_closed positiveUnary failureUnary conflictRoute
  · constructor
    · rw [fieldsExact]
      exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · rw [fieldsExact]
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · rw [fieldsExact]
        exact
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ (List.Mem.head _)

theorem AuditExportFirewallCarrier_namecert_obligations
    {claim positive audit failure registry consistency ledger transport replay provenance name
      gateRead replayRead : BHist} :
    UnaryHistory claim ->
      UnaryHistory positive ->
        UnaryHistory audit ->
          UnaryHistory failure ->
            UnaryHistory registry ->
              UnaryHistory consistency ->
                UnaryHistory ledger ->
                  UnaryHistory transport ->
                    UnaryHistory replay ->
                      UnaryHistory provenance ->
                        UnaryHistory name ->
                          Cont positive failure gateRead ->
                            Cont ledger replay replayRead ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row claim ∨ hsame row positive ∨ hsame row failure ∨
                                      hsame row ledger ∨ hsame row gateRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont positive failure gateRead)
                                  hsame ∧
                                UnaryHistory gateRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro _claimUnary positiveUnary _auditUnary failureUnary _registryUnary _consistencyUnary
    ledgerUnary _transportUnary replayUnary _provenanceUnary _nameUnary gateRoute replayRoute
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed positiveUnary failureUnary gateRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed ledgerUnary replayUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row claim ∨ hsame row positive ∨ hsame row failure ∨
              hsame row ledger ∨ hsame row gateRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont positive failure gateRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gateRead ⟨hsame_refl gateRead, gateUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gateRoute⟩
  }
  exact ⟨cert, gateUnary, replayReadUnary⟩

end BEDC.Derived.AuditExportFirewallUp
