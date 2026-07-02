import BEDC.Derived.DimLiftBoundaryUp

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DimLiftBoundaryCarrier_admission_obligation
    {Z N A F R H C P Q admissionRead : BHist} :
    Cont Z N admissionRead →
      SemanticNameCert
          (fun row : BHist => hsame row admissionRead)
          (fun row : BHist =>
            hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row Q ∨ hsame row admissionRead)
          (fun _row : BHist => Cont Z N admissionRead)
          hsame ∧
        Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro admissionRoute
  constructor
  · constructor
    · constructor
      · exact Exists.intro admissionRead (hsame_refl admissionRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source
    · intro _row _source
      exact admissionRoute
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

end BEDC.Derived.DimLiftBoundaryUp
