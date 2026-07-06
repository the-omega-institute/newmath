import BEDC.Derived.MetacicDecidableAuditPacketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetacicDecidableAuditPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

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

theorem MetacicDecidableAuditPacket_scoped_kernel_route
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName typedWindow normalWindow structuralWindow boundaryWindow : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker typing typedWindow ∧
          Cont boundedNormal boundary normalWindow ∧
            Cont transport replay structuralWindow ∧
              Cont normalWindow obstruction boundaryWindow ∧
                metacicDecidableAuditPacketFromEventFlow
                    (metacicDecidableAuditPacketToEventFlow x) =
                  some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, append checker typing, append boundedNormal boundary,
          append transport replay, append (append boundedNormal boundary) obstruction, rfl, rfl,
          rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)⟩

theorem MetacicDecidableAuditPacket_checker_boundary_semantic_certificate
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay provenance
        localName checkerWindow boundaryWindow auditWindow : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker sameTerm checkerWindow ∧
          Cont boundedNormal obstruction boundaryWindow ∧
            Cont checkerWindow boundaryWindow auditWindow ∧
              SemanticNameCert
                (fun row : BHist => hsame row auditWindow)
                (fun row : BHist =>
                  hsame row checker ∨ hsame row sameTerm ∨ hsame row boundedNormal ∨
                    hsame row obstruction ∨ hsame row auditWindow)
                (fun row : BHist =>
                  hsame row auditWindow ∧ Cont checker sameTerm checkerWindow ∧
                    Cont boundedNormal obstruction boundaryWindow ∧
                      Cont checkerWindow boundaryWindow auditWindow)
                hsame := by
  -- BEDC touchpoint anchor: BHist BMark Cont SemanticNameCert hsame
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      let checkerWindow := append checker sameTerm
      let boundaryWindow := append boundedNormal obstruction
      let auditWindow := append checkerWindow boundaryWindow
      have checkerRoute : Cont checker sameTerm checkerWindow := rfl
      have boundaryRoute : Cont boundedNormal obstruction boundaryWindow := rfl
      have auditRoute : Cont checkerWindow boundaryWindow auditWindow := rfl
      have cert :
          SemanticNameCert
            (fun row : BHist => hsame row auditWindow)
            (fun row : BHist =>
              hsame row checker ∨ hsame row sameTerm ∨ hsame row boundedNormal ∨
                hsame row obstruction ∨ hsame row auditWindow)
            (fun row : BHist =>
              hsame row auditWindow ∧ Cont checker sameTerm checkerWindow ∧
                Cont boundedNormal obstruction boundaryWindow ∧
                  Cont checkerWindow boundaryWindow auditWindow)
            hsame := {
        core := {
          carrier_inhabited := Exists.intro auditWindow (hsame_refl auditWindow)
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
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr source)))
        ledger_sound := by
          intro _row source
          exact ⟨source, checkerRoute, boundaryRoute, auditRoute⟩
      }
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, checkerWindow, boundaryWindow, auditWindow, rfl,
          checkerRoute, boundaryRoute, auditRoute, cert⟩

theorem MetacicDecidableAuditPacket_retained_normal_window
    (x : MetacicDecidableAuditPacketUp) :
    ∃ checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName checkerRead typingRead galleryRead boundedRead boundaryRead
        retainedRead : BHist,
      x =
          MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
            boundary obstruction transport replay provenance localName ∧
        Cont checker sameTerm checkerRead ∧
          Cont checkerRead typing typingRead ∧
            Cont typingRead gallery galleryRead ∧
              Cont galleryRead boundedNormal boundedRead ∧
                Cont boundedRead boundary boundaryRead ∧
                  Cont boundaryRead obstruction retainedRead ∧
                    metacicDecidableAuditPacketFromEventFlow
                        (metacicDecidableAuditPacketToEventFlow x) =
                      some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      exact
        ⟨checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName, append checker sameTerm,
          append (append checker sameTerm) typing,
          append (append (append checker sameTerm) typing) gallery,
          append (append (append (append checker sameTerm) typing) gallery) boundedNormal,
          append
            (append (append (append (append checker sameTerm) typing) gallery) boundedNormal)
            boundary,
          append
            (append
              (append (append (append (append checker sameTerm) typing) gallery) boundedNormal)
              boundary)
            obstruction,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          MetacicDecidableAuditPacketTasteGate_single_carrier_alignment.right.left
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)⟩

end BEDC.Derived.MetacicDecidableAuditPacketUp
