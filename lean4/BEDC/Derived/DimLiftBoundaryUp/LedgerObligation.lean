import BEDC.Derived.DimLiftBoundaryUp

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DimLiftBoundaryCarrier_ledger_obligation
    {Z N A F R H C P Q consumerRead refusalRead : BHist} :
    Cont C Q consumerRead →
      Cont A R refusalRead →
        hsame consumerRead refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row P ∨ hsame row Q ∨ hsame row consumerRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
                    hsame row consumerRead ∨ hsame row refusalRead)
              (fun row : BHist => Cont C Q consumerRead ∧ Cont A R refusalRead ∧ hsame row row)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro consumerRoute refusalRoute sameBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row P ∨ hsame row Q ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
                hsame row consumerRead ∨ hsame row refusalRead)
          (fun row : BHist => Cont C Q consumerRead ∧ Cont A R refusalRead ∧ hsame row row)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Q (Or.inr (Or.inl (hsame_refl Q)))
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
        intro row other sameRows source
        cases source with
        | inl rowP =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowP)
        | inr rest =>
            cases rest with
            | inl rowQ =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowQ))
            | inr rowConsumer =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowConsumer))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl rowP =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl rowP)))))))
      | inr rest =>
          cases rest with
          | inl rowQ =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl rowQ))))))))
          | inr rowConsumer =>
              have rowRefusal : hsame row refusalRead :=
                hsame_trans rowConsumer sameBoundary
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr rowRefusal)))))))))
    ledger_sound := by
      intro row _source
      exact ⟨consumerRoute, refusalRoute, hsame_refl row⟩
  }
  exact ⟨cert, Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)⟩

end BEDC.Derived.DimLiftBoundaryUp
