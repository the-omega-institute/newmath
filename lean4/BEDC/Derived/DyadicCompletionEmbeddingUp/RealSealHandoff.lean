import BEDC.Derived.DyadicCompletionEmbeddingUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicCompletionEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DyadicCompletionEmbeddingRealSealHandoff :
    ∀ x : BEDC.Derived.DyadicCompletionEmbeddingUp,
      ∃ source streamWindow regularReadback realSeal criterion transport replay provenance
          namecert : BHist,
        x =
            BEDC.Derived.DyadicCompletionEmbeddingUp.carrier source streamWindow
              regularReadback realSeal criterion transport replay provenance namecert ∧
          SemanticNameCert
            (fun row : BHist => hsame row realSeal)
            (fun row : BHist =>
              hsame row source ∨ hsame row streamWindow ∨ hsame row regularReadback ∨
                hsame row realSeal ∨ hsame row criterion ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row namecert)
            (fun row : BHist =>
              hsame row realSeal ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row namecert)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  intro x
  cases x with
  | carrier source streamWindow regularReadback realSeal criterion transport replay
      provenance namecert =>
      refine
        ⟨source, streamWindow, regularReadback, realSeal, criterion, transport, replay,
          provenance, namecert, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := Exists.intro realSeal (hsame_refl realSeal)
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
            intro _row _other sameRows sourceSame
            exact hsame_trans (hsame_symm sameRows) sourceSame
        }
        pattern_sound := by
          intro _row sourceSame
          exact Or.inr (Or.inr (Or.inr (Or.inl sourceSame)))
        ledger_sound := by
          intro _row sourceSame
          exact Or.inl sourceSame
      }

end BEDC.Derived.DyadicCompletionEmbeddingUp
