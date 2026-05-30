import BEDC.Derived.LocatedLimitUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LocatedLimitCarrier_namecert_obligations
    (sequence modulus schedule readback sealRow transport replay provenance name : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row provenance ∧
          locatedLimitFields
              (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay
                provenance name) =
            [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance,
              name])
      (fun row : BHist =>
        hsame row provenance ∧
          locatedLimitFields
              (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay
                provenance name) =
            [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance,
              name])
      (fun row : BHist =>
        hsame row provenance ∧
          locatedLimitFields
              (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay
                provenance name) =
            [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance,
              name])
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  let fields :=
    locatedLimitFields
      (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay provenance
        name)
  let expected :=
    [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance, name]
  have sourceProvenance :
      (fun row : BHist => hsame row provenance ∧ fields = expected) provenance := by
    exact And.intro (hsame_refl provenance) rfl
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance sourceProvenance
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.LocatedLimitUp
