import BEDC.Derived.CertifiedPhysicalTruthUp.TasteGate

namespace BEDC.Derived.CertifiedPhysicalTruthUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem CertifiedPhysicalTruth_obligation_surface_row_injective
    {S G K A D I L F H C P N S' G' K' A' D' I' L' F' H' C' P' N' : BHist}
    (hflow :
      BHistCarrier.toEventFlow (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N) =
        BHistCarrier.toEventFlow (CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N')) :
    S = S' ∧ G = G' ∧ K = K' ∧ A = A' ∧ D = D' ∧ I = I' ∧ L = L' ∧ F = F' ∧
      certifiedPhysicalTruthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, certifiedPhysicalTruthDecodeBHist
        (certifiedPhysicalTruthEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  change
    certifiedPhysicalTruthToEventFlow (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N) =
      certifiedPhysicalTruthToEventFlow
        (CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N') at hflow
  have hread :
      certifiedPhysicalTruthFromEventFlow
          (certifiedPhysicalTruthToEventFlow (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N)) =
        certifiedPhysicalTruthFromEventFlow
          (certifiedPhysicalTruthToEventFlow
            (CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N')) :=
    congrArg certifiedPhysicalTruthFromEventFlow hflow
  change
    some
        (CertifiedPhysicalTruthUp.mk
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist S))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist G))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist K))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist A))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist D))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist I))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist L))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist F))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist H))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist C))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist P))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist N))) =
      some
        (CertifiedPhysicalTruthUp.mk
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist S'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist G'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist K'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist A'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist D'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist I'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist L'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist F'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist H'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist C'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist P'))
          (certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist N'))) at hread
  rw [hdecode S, hdecode G, hdecode K, hdecode A, hdecode D, hdecode I, hdecode L,
    hdecode F, hdecode H, hdecode C, hdecode P, hdecode N, hdecode S', hdecode G',
    hdecode K', hdecode A', hdecode D', hdecode I', hdecode L', hdecode F',
    hdecode H', hdecode C', hdecode P', hdecode N'] at hread
  injection hread with hpacket
  injection hpacket with hS hG hK hA hD hI hL hF _ _ _ _
  exact ⟨hS, hG, hK, hA, hD, hI, hL, hF, rfl⟩

theorem CertifiedPhysicalTruth_carrier_row_injective
    {S G K A D I L F H C P N S' G' K' A' D' I' L' F' H' C' P' N' : BHist}
    (hflow :
      BHistCarrier.toEventFlow (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N) =
        BHistCarrier.toEventFlow
          (CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N')) :
    S = S' ∧ G = G' ∧ K = K' ∧ A = A' ∧ D = D' ∧ I = I' ∧ L = L' ∧ F = F' ∧
      H = H' ∧ C = C' ∧ P = P' ∧ N = N' ∧
        certifiedPhysicalTruthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hpacket :
      CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N =
        CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N' := by
    change
      certifiedPhysicalTruthToEventFlow (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N) =
        certifiedPhysicalTruthToEventFlow
          (CertifiedPhysicalTruthUp.mk S' G' K' A' D' I' L' F' H' C' P' N') at hflow
    exact CertifiedPhysicalTruthTasteGate_single_carrier_alignment.right.right.left _ _ hflow
  injection hpacket with hS hG hK hA hD hI hL hF hH hC hP hN
  exact ⟨hS, hG, hK, hA, hD, hI, hL, hF, hH, hC, hP, hN, rfl⟩

end BEDC.Derived.CertifiedPhysicalTruthUp
