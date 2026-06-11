import BEDC.Derived.AxisUnarySpineNormalizerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AxisUnarySpineNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem AxisUnarySpineNormalizerNameCertObligations (x : AxisUnarySpineNormalizerUp) :
    ∃ sourceSpine axisZeroSpine lengthLedger standardBoundary componentTransport
        continuationRoutes provenance name : BHist,
      x = AxisUnarySpineNormalizerUp.mk sourceSpine axisZeroSpine lengthLedger
        standardBoundary componentTransport continuationRoutes provenance name ∧
        SemanticNameCert
          (fun row : BHist => hsame row name)
          (fun row : BHist =>
            hsame row sourceSpine ∨ hsame row axisZeroSpine ∨ hsame row lengthLedger ∨
              hsame row standardBoundary ∨ hsame row componentTransport ∨
                hsame row continuationRoutes ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            hsame row sourceSpine ∨ hsame row axisZeroSpine ∨ hsame row lengthLedger ∨
              hsame row standardBoundary ∨ hsame row componentTransport ∨
                hsame row continuationRoutes ∨ hsame row provenance ∨ hsame row name)
          hsame ∧
          Cont BHist.Empty sourceSpine sourceSpine ∧
            Cont BHist.Empty axisZeroSpine axisZeroSpine ∧
              Cont BHist.Empty standardBoundary standardBoundary := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  cases x with
  | mk sourceSpine axisZeroSpine lengthLedger standardBoundary componentTransport
      continuationRoutes provenance name =>
      let rowSurface := fun row : BHist =>
        hsame row sourceSpine ∨ hsame row axisZeroSpine ∨ hsame row lengthLedger ∨
          hsame row standardBoundary ∨ hsame row componentTransport ∨
            hsame row continuationRoutes ∨ hsame row provenance ∨ hsame row name
      have nameCert :
          SemanticNameCert (fun row : BHist => hsame row name) rowSurface rowSurface hsame := {
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
            intro _row _other sameRows source
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
        ledger_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
      }
      exact
        ⟨sourceSpine, axisZeroSpine, lengthLedger, standardBoundary, componentTransport,
          continuationRoutes, provenance, name, rfl, nameCert, cont_left_unit sourceSpine,
          cont_left_unit axisZeroSpine, cont_left_unit standardBoundary⟩

end BEDC.Derived.AxisUnarySpineNormalizerUp
