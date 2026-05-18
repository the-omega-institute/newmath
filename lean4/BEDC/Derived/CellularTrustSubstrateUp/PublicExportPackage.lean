import BEDC.Derived.CellularTrustSubstrateUp.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CellularTrustSubstrate_public_export_package
    {R W K M A H C P N publicRead : BHist}
    (ruleRoute : Cont R W K)
    (manifestRoute : Cont K M A)
    (auditPublic : Cont A N publicRead) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : TasteGate.CellularTrustSubstrateUp,
              packet = TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist => hsame row R ∧ Cont R W K ∧ Cont K M A ∧ hsame C C)
        (fun row : BHist => hsame row R ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame ∧
      Cont R W K ∧ Cont K M A ∧ Cont A N publicRead ∧
        hsame H H ∧ hsame P P ∧ hsame N N ∧
          TasteGate.cellularTrustSubstrateToEventFlow
              (TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N) =
            TasteGate.cellularTrustSubstrateToEventFlow
              (TasteGate.CellularTrustSubstrateUp.mk R W K M A H C P N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have surface :=
    TasteGate.CellularTrustSubstrate_obligation_surface
      (R := R) (W := W) (K := K) (M := M) (A := A) (H := H) (C := C)
      (P := P) (N := N) ruleRoute manifestRoute
  obtain ⟨cert, eventFlowStable⟩ := surface
  exact
    ⟨cert, ruleRoute, manifestRoute, auditPublic, hsame_refl H, hsame_refl P,
      hsame_refl N, eventFlowStable⟩

end BEDC.Derived.CellularTrustSubstrateUp
