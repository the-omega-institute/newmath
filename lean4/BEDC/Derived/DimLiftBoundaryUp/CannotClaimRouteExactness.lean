import BEDC.Derived.DimLiftBoundaryUp

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DimLiftBoundaryCarrier_cannot_claim_route_exactness
    {Z N A F R H C P Q axisRead refusalRead boundaryRead : BHist} :
    Cont Z N axisRead ->
      Cont A R refusalRead ->
        Cont axisRead refusalRead boundaryRead ->
          SemanticNameCert
              (fun row : BHist => hsame row boundaryRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row R ∨
                  hsame row axisRead ∨ hsame row refusalRead ∨ hsame row boundaryRead)
              (fun _row : BHist =>
                Cont Z N axisRead ∧ Cont A R refusalRead ∧
                  Cont axisRead refusalRead boundaryRead)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro axisRoute refusalRoute boundaryRoute
  constructor
  · constructor
    · constructor
      · exact Exists.intro boundaryRead (hsame_refl boundaryRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source)))))
    · intro _row _source
      exact ⟨axisRoute, refusalRoute, boundaryRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

end BEDC.Derived.DimLiftBoundaryUp
