import BEDC.Derived.DimLiftBoundaryUp

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DimLiftBoundaryDownstreamAcceptanceBoundary
    {Z N A F R H C P Q acceptanceRead refusalRead lockedRead : BHist} :
    Cont Z N lockedRead ->
      Cont A R refusalRead ->
        Cont lockedRead Q acceptanceRead ->
          hsame acceptanceRead refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row acceptanceRead)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
                    hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row Q ∨ hsame row lockedRead ∨ hsame row acceptanceRead ∨
                        hsame row refusalRead)
                (fun _row : BHist =>
                  Cont Z N lockedRead ∧ Cont A R refusalRead ∧
                    Cont lockedRead Q acceptanceRead)
                hsame ∧
              Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro lockedRoute refusalRoute acceptanceRoute _sameBoundary
  constructor
  · constructor
    · constructor
      · exact Exists.intro acceptanceRead (hsame_refl acceptanceRead)
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
      apply Or.inr
      exact Or.inl source
    · intro _row _source
      exact ⟨lockedRoute, refusalRoute, acceptanceRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

end BEDC.Derived.DimLiftBoundaryUp
