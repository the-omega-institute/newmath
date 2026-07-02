import BEDC.Derived.MetacicDecidableAuditPacketUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.MetacicDecidableAuditPacketUp

open BEDC.FKernel.Cont
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

theorem MetacicDecidableAuditPacket_typed_conversion_window_obligation_surface
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName typedWindow normalWindow auditWindow : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker typing typedWindow ∧
          Cont boundedNormal boundary normalWindow ∧
            Cont typedWindow normalWindow auditWindow ∧
              metacicDecidableAuditPacketFromEventFlow
                  (metacicDecidableAuditPacketToEventFlow x) =
                some x ∧
                metacicDecidableAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, append checker typing,
          append boundedNormal boundary, append (append checker typing) (append boundedNormal boundary),
          rfl, rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName),
          rfl⟩

end BEDC.Derived.MetacicDecidableAuditPacketUp
