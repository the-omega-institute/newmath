import BEDC.Derived.FullAxisRealRefusalUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FullAxisRealRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

theorem FullAxisRealRefusal_non_escape (q : FullAxisRealRefusalUp) :
    ∃ fullAxis refusal cannotClaim transport route provenance name : BHist,
      q =
          FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name ∧
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow q) = some q ∧
          fullAxisRealRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases q with
  | mk fullAxis refusal cannotClaim transport route provenance name =>
      exact
        ⟨fullAxis, refusal, cannotClaim, transport, route, provenance, name, rfl,
          FullAxisRealRefusalTasteGate_single_carrier_alignment.right.left
            (FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name),
          rfl⟩

theorem FullAxisRealRefusal_namecert_obligations (q : FullAxisRealRefusalUp) :
    ∃ fullAxis refusal cannotClaim transport route provenance name : BHist,
      q = FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name ∧
        SemanticNameCert
          (fun row : BHist => hsame row name)
          (fun row : BHist =>
            hsame row fullAxis ∨ hsame row refusal ∨ hsame row cannotClaim ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim ∨
              row = BHist.Empty)
          hsame ∧
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow q) = some q := by
  -- BEDC touchpoint anchor: BHist BMark hsame SemanticNameCert
  cases q with
  | mk fullAxis refusal cannotClaim transport route provenance name =>
      have cert :
          SemanticNameCert
            (fun row : BHist => hsame row name)
            (fun row : BHist =>
              hsame row fullAxis ∨ hsame row refusal ∨ hsame row cannotClaim ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
            (fun row : BHist =>
              hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim ∨
                row = BHist.Empty)
            hsame := {
        core := {
          carrier_inhabited := Exists.intro name (hsame_refl name)
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
            intro _row _other sameRows sourceRow
            exact hsame_trans (hsame_symm sameRows) sourceRow
        }
        pattern_sound := by
          intro _row sourceRow
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow)))))
        ledger_sound := by
          intro _row sourceRow
          exact Or.inl sourceRow
      }
      exact
        ⟨fullAxis, refusal, cannotClaim, transport, route, provenance, name, rfl, cert,
          FullAxisRealRefusalTasteGate_single_carrier_alignment.right.left
            (FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name)⟩

theorem FullAxisRealRefusal_vision_concretization (q : FullAxisRealRefusalUp) :
    ∃ fullAxis refusal cannotClaim transport route provenance name : BHist,
      q = FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name ∧
        SemanticNameCert
          (fun row : BHist =>
            hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim)
          (fun row : BHist =>
            hsame row fullAxis ∨ hsame row refusal ∨ hsame row cannotClaim ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim)
          hsame ∧
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow q) = some q := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases q with
  | mk fullAxis refusal cannotClaim transport route provenance name =>
      have core :
          NameCert
            (fun row : BHist =>
              hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim)
            hsame := {
        carrier_inhabited := Exists.intro name (Or.inl (hsame_refl name))
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
          intro _row _other sameRows sourceRow
          cases sourceRow with
          | inl sameName =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameName)
          | inr rest =>
              cases rest with
              | inl sameRefusal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefusal))
              | inr sameCannotClaim =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCannotClaim))
      }
      have patternSound :
          ∀ {row : BHist},
            (hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim) →
              hsame row fullAxis ∨ hsame row refusal ∨ hsame row cannotClaim ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row name := by
        intro _row sourceRow
        cases sourceRow with
        | inl sameName =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          sameName)))))
        | inr rest =>
            cases rest with
            | inl sameRefusal =>
                exact Or.inr (Or.inl sameRefusal)
            | inr sameCannotClaim =>
                exact Or.inr (Or.inr (Or.inl sameCannotClaim))
      have cert :
          SemanticNameCert
            (fun row : BHist =>
              hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim)
            (fun row : BHist =>
              hsame row fullAxis ∨ hsame row refusal ∨ hsame row cannotClaim ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
            (fun row : BHist =>
              hsame row name ∨ hsame row refusal ∨ hsame row cannotClaim)
            hsame :=
        SemanticNameCert.mk core patternSound (by
          intro _row sourceRow
          exact sourceRow)
      exact
        ⟨fullAxis, refusal, cannotClaim, transport, route, provenance, name, rfl, cert,
          FullAxisRealRefusalTasteGate_single_carrier_alignment.right.left
            (FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name)⟩

end BEDC.Derived.FullAxisRealRefusalUp
