import BEDC.Derived.DedekindCutBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DedekindCutBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DedekindCutBoundaryNameCertObligations :
    ∀ x : BEDC.Derived.DedekindCutBoundaryUp,
      ∃ locatedCut dedekindReal comparison regularReadback streamWindow dyadicTolerance
          realSeal transport replay provenance name : BHist,
        x =
            BEDC.Derived.DedekindCutBoundaryUp.mk locatedCut dedekindReal comparison
              regularReadback streamWindow dyadicTolerance realSeal transport replay provenance
              name ∧
          SemanticNameCert
            (fun row : BHist => hsame row name)
            (fun row : BHist =>
              hsame row locatedCut ∨ hsame row dedekindReal ∨ hsame row comparison ∨
                hsame row regularReadback ∨ hsame row streamWindow ∨
                  hsame row dyadicTolerance ∨ hsame row realSeal ∨ hsame row transport ∨
                    hsame row replay ∨ hsame row provenance ∨ hsame row name)
            (fun row : BHist =>
              hsame row comparison ∨ hsame row regularReadback ∨ hsame row realSeal ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  intro x
  cases x with
  | mk locatedCut dedekindReal comparison regularReadback streamWindow dyadicTolerance
      realSeal transport replay provenance name =>
      exact
        ⟨locatedCut, dedekindReal, comparison, regularReadback, streamWindow, dyadicTolerance,
          realSeal, transport, replay, provenance, name, rfl,
          {
            core := {
              carrier_inhabited := ⟨name, hsame_refl name⟩
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
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr (Or.inr source)))))))))
            ledger_sound := by
              intro _row source
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))
          }⟩

end BEDC.Derived.DedekindCutBoundaryUp
