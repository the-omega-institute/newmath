import BEDC.Derived.PhysicalRecordInvariantUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PhysicalRecordInvariantUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhysicalRecordInvariantCarrier_classifier_stability
    {R I O H C P N R' I' O' H' C' P' N' replay replay' : BHist} :
    hsame R R' -> hsame I I' -> hsame O O' -> hsame H H' -> hsame C C' ->
      hsame P P' -> hsame N N' -> Cont H C replay -> Cont H' C' replay' ->
        SemanticNameCert
            (fun row : BHist =>
              hsame row N ∧ hsame R R' ∧ hsame I I' ∧ hsame O O' ∧ hsame H H' ∧
                hsame C C' ∧ hsame P P' ∧ hsame N N')
            (fun row : BHist =>
              hsame row N ∧ Cont H C replay ∧ Cont H' C' replay')
            (fun row : BHist => hsame row N ∧ hsame replay replay')
            hsame ∧
          hsame replay replay' := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro sameR sameI sameO sameH sameC sameP sameN replayRoute replayRoute'
  have sameReplay : hsame replay replay' :=
    cont_respects_hsame sameH sameC replayRoute replayRoute'
  have sourceN :
      hsame N N ∧ hsame R R' ∧ hsame I I' ∧ hsame O O' ∧ hsame H H' ∧
        hsame C C' ∧ hsame P P' ∧ hsame N N' :=
    ⟨hsame_refl N, sameR, sameI, sameO, sameH, sameC, sameP, sameN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ hsame R R' ∧ hsame I I' ∧ hsame O O' ∧ hsame H H' ∧
              hsame C C' ∧ hsame P P' ∧ hsame N N')
          (fun row : BHist =>
            hsame row N ∧ Cont H C replay ∧ Cont H' C' replay')
          (fun row : BHist => hsame row N ∧ hsame replay replay')
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            source.right.left,
            source.right.right.left,
            source.right.right.right.left,
            source.right.right.right.right.left,
            source.right.right.right.right.right.left,
            source.right.right.right.right.right.right.left,
            source.right.right.right.right.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, replayRoute, replayRoute'⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameReplay⟩
  }
  exact ⟨cert, sameReplay⟩

end BEDC.Derived.PhysicalRecordInvariantUp
