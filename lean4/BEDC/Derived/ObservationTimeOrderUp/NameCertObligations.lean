import BEDC.Derived.ObservationTimeOrderUp.TasteGate

namespace BEDC.Derived.ObservationTimeOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ObservationTimeOrderNameCertObligations (O0 O1 R C G H P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        hsame ∧
      observationTimeOrderFields (ObservationTimeOrderUp.mk O0 O1 R C G H P N) =
        [O0, O1, R, C, G, H, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  have base := ObservationTimeOrderNo_host_time_nonescape O0 O1 R C G H P N
  exact ⟨NameCert_carrier_self_semantic_lifting base.left, base.right⟩

end BEDC.Derived.ObservationTimeOrderUp
