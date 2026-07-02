import BEDC.Derived.MetacicDecidableAuditPacketUp.TasteGate

namespace BEDC.Derived.MetacicDecidableAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem MetacicDecidableAuditPacket_seed_obligation_surface
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        metacicDecidableAuditPacketFromEventFlow (metacicDecidableAuditPacketToEventFlow x) =
          some x ∧
          metacicDecidableAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName),
          rfl⟩

end BEDC.Derived.MetacicDecidableAuditPacketUp
