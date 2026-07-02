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

theorem MetacicDecidableAuditPacket_bounded_normal_boundary
    (x : MetacicDecidableAuditPacketUp) :
    ∃ boundedNormal boundary obstruction normalWindow boundaryWindow : BHist,
      (∃ checker sameTerm typing gallery transport replay provenance localName : BHist,
        x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName) ∧
        Cont boundedNormal boundary normalWindow ∧
          Cont normalWindow obstruction boundaryWindow ∧
            metacicDecidableAuditPacketFromEventFlow
                (metacicDecidableAuditPacketToEventFlow x) =
              some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨boundedNormal, boundary, obstruction, append boundedNormal boundary,
          append (append boundedNormal boundary) obstruction,
          ⟨checker, sameTerm, typing, gallery, transport, replay, provenance, localName, rfl⟩,
          rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)⟩

theorem MetacicDecidableAuditPacket_checker_exactness_route
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay provenance
        localName checkerRead sameTermRead auditRead : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker typing checkerRead ∧
          Cont sameTerm typing sameTermRead ∧
            Cont checkerRead gallery auditRead ∧
              metacicDecidableAuditPacketFromEventFlow
                  (metacicDecidableAuditPacketToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, append checker typing, append sameTerm typing,
          append (append checker typing) gallery, rfl, rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)⟩

theorem MetacicDecidableAuditPacket_nonescape
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay provenance
        localName replayRead boundaryRead : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont transport replay replayRead ∧
          Cont boundary obstruction boundaryRead ∧
            metacicDecidableAuditPacketFromEventFlow
                (metacicDecidableAuditPacketToEventFlow x) =
              some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, append transport replay, append boundary obstruction,
          rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)⟩

theorem MetacicDecidableAuditPacket_obligation_closure_surface
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName checkerWindow normalWindow structuralWindow namedWindow : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker sameTerm checkerWindow ∧
          Cont boundedNormal boundary normalWindow ∧
            Cont transport replay structuralWindow ∧
              Cont provenance localName namedWindow ∧
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
          replay, provenance, localName, append checker sameTerm, append boundedNormal boundary,
          append transport replay, append provenance localName, rfl, rfl, rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName),
          rfl⟩

end BEDC.Derived.MetacicDecidableAuditPacketUp
