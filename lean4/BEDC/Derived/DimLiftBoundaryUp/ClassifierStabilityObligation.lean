import BEDC.Derived.DimLiftBoundaryUp.CarrierAdmissionObligation

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DimLiftBoundaryCarrier_classifier_stability_obligation
    {Z N A F R H C P Q Zp Np Ap Fp Rp Hp _Cp Pp Qp : BHist}
    (sameZ : hsame Z Zp)
    (sameN : hsame N Np)
    (sameA : hsame A Ap)
    (sameF : hsame F Fp)
    (sameR : hsame R Rp)
    (sameP : hsame P Pp)
    (sameQ : hsame Q Qp)
    (route : Cont H C Hp) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
            hsame row R ∨ hsame row P ∨ hsame row Q)
        (fun row : BHist =>
          hsame row Zp ∨ hsame row Np ∨ hsame row Ap ∨ hsame row Fp ∨
            hsame row Rp ∨ hsame row Pp ∨ hsame row Qp ∨ hsame row Hp)
        (fun row : BHist =>
          Cont H C Hp ∧
            (hsame row Zp ∨ hsame row Np ∨ hsame row Ap ∨ hsame row Fp ∨
              hsame row Rp ∨ hsame row Pp ∨ hsame row Qp))
        hsame ∧
      Cont H C Hp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  have transportLedger :
      ∀ {row : BHist},
        (hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
          hsame row R ∨ hsame row P ∨ hsame row Q) →
          hsame row Zp ∨ hsame row Np ∨ hsame row Ap ∨ hsame row Fp ∨
            hsame row Rp ∨ hsame row Pp ∨ hsame row Qp := by
    intro row source
    cases source with
    | inl sameRowZ =>
        exact Or.inl (hsame_trans sameRowZ sameZ)
    | inr rest =>
        cases rest with
        | inl sameRowN =>
            exact Or.inr (Or.inl (hsame_trans sameRowN sameN))
        | inr rest =>
            cases rest with
            | inl sameRowA =>
                exact Or.inr (Or.inr (Or.inl (hsame_trans sameRowA sameA)))
            | inr rest =>
                cases rest with
                | inl sameRowF =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans sameRowF sameF))))
                | inr rest =>
                    cases rest with
                    | inl sameRowR =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl (hsame_trans sameRowR sameR)))))
                    | inr rest =>
                        cases rest with
                        | inl sameRowP =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl (hsame_trans sameRowP sameP))))))
                        | inr sameRowQ =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr (hsame_trans sameRowQ sameQ))))))
  have transportPattern :
      ∀ {row : BHist},
        (hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
          hsame row R ∨ hsame row P ∨ hsame row Q) →
          hsame row Zp ∨ hsame row Np ∨ hsame row Ap ∨ hsame row Fp ∨
            hsame row Rp ∨ hsame row Pp ∨ hsame row Qp ∨ hsame row Hp := by
    intro row source
    cases transportLedger source with
    | inl sameRowZp =>
        exact Or.inl sameRowZp
    | inr rest =>
        cases rest with
        | inl sameRowNp =>
            exact Or.inr (Or.inl sameRowNp)
        | inr rest =>
            cases rest with
            | inl sameRowAp =>
                exact Or.inr (Or.inr (Or.inl sameRowAp))
            | inr rest =>
                cases rest with
                | inl sameRowFp =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl sameRowFp)))
                | inr rest =>
                    cases rest with
                    | inl sameRowRp =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRowRp))))
                    | inr rest =>
                        cases rest with
                        | inl sameRowPp =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl sameRowPp)))))
                        | inr sameRowQp =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr (Or.inl sameRowQp))))))
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro Z (Or.inl (hsame_refl Z))
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
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro _row source
        exact transportPattern source
      ledger_sound := by
        intro _row source
        exact And.intro route (transportLedger source)
    }
  · exact route

end BEDC.Derived.DimLiftBoundaryUp
