import BEDC.Derived.MachineInterfaceBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MachineInterfaceBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MachineInterfaceBoundary_paper_bridge_certificate
    {R E F A S H C P N registryExport socketAudit bridgeRead : BHist} :
    UnaryHistory R ->
      UnaryHistory E ->
        UnaryHistory S ->
          UnaryHistory N ->
            Cont R E registryExport ->
              Cont registryExport S socketAudit ->
                Cont socketAudit N bridgeRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row R ∨ hsame row E ∨ hsame row F ∨ hsame row A ∨
                          hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row bridgeRead)
                      (fun row : BHist =>
                        hsame row bridgeRead ∧ Cont R E registryExport ∧
                          Cont registryExport S socketAudit ∧ Cont socketAudit N bridgeRead)
                      hsame ∧
                    machineInterfaceBoundaryFields
                        (MachineInterfaceBoundaryUp.packet R E F A S H C P N) =
                      [R, E, F, A, S, H, C, P, N] ∧
                      UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryR unaryE unaryS unaryN routeExport routeAudit routeBridge
  have unaryRegistryExport : UnaryHistory registryExport :=
    unary_cont_closed unaryR unaryE routeExport
  have unarySocketAudit : UnaryHistory socketAudit :=
    unary_cont_closed unaryRegistryExport unaryS routeAudit
  have unaryBridgeRead : UnaryHistory bridgeRead :=
    unary_cont_closed unarySocketAudit unaryN routeBridge
  have sourceAtBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, unaryBridgeRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row E ∨ hsame row F ∨ hsame row A ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            hsame row bridgeRead ∧ Cont R E registryExport ∧
              Cont registryExport S socketAudit ∧ Cont socketAudit N bridgeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeExport, routeAudit, routeBridge⟩
  }
  exact ⟨cert, rfl, unaryBridgeRead⟩

end BEDC.Derived.MachineInterfaceBoundaryUp
