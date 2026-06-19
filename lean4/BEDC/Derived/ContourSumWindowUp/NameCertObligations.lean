import BEDC.Derived.ContourSumWindowUp.TasteGate
import BEDC.FKernel.NameCert

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

namespace BEDC.Derived.ContourSumWindowUp

theorem ContourSumWindowNameCertObligations
    {contour holomorphic subdivision riemann output transport continuation provenance name :
      BHist} :
    SemanticNameCert
        (fun row : BHist => hsame row name)
        (fun row : BHist =>
          hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
            hsame row riemann ∨ hsame row output ∨ hsame row transport ∨
              hsame row continuation ∨ hsame row provenance ∨ hsame row name)
        (fun row : BHist =>
          hsame row name ∧ hsame subdivision subdivision ∧ hsame riemann riemann ∧
            hsame output output ∧ hsame continuation continuation)
        hsame ∧
      ContourSumWindowUp.mk contour holomorphic subdivision riemann output transport continuation
          provenance name =
        ContourSumWindowUp.mk contour holomorphic subdivision riemann output transport continuation
          provenance name := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name)
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
              hsame row riemann ∨ hsame row output ∨ hsame row transport ∨
                hsame row continuation ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            hsame row name ∧ hsame subdivision subdivision ∧ hsame riemann riemann ∧
              hsame output output ∧ hsame continuation continuation)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name (hsame_refl name)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source, hsame_refl subdivision, hsame_refl riemann, hsame_refl output,
          hsame_refl continuation⟩
  }
  exact ⟨cert, rfl⟩

end BEDC.Derived.ContourSumWindowUp
