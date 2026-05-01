import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SumHistoryClassifier_right_hsame_inversion {Left Right : BHist -> Prop}
    {l r : BHist} :
    SumHistoryClassifier Left Right hsame hsame (BHist.e1 l) (BHist.e1 r) -> hsame l r := by
  intro classifier
  cases classifier with
  | inl leftData =>
      cases leftData with
      | intro left0 rest =>
          cases rest with
          | intro _ data =>
              exact False.elim (not_hsame_e1_e0 data.left)
  | inr rightData =>
      cases rightData with
      | intro right0 rest =>
          cases rest with
          | intro right1 data =>
              exact hsame_trans (hsame_trans (hsame_e1_iff.mp data.left) data.right.right)
                (hsame_symm (hsame_e1_iff.mp data.right.left))

theorem SumHistoryClassifier_carrier_transport_from_nameCert {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq) {h k : BHist} :
    SumHistoryCarrier Left Right h ->
      SumHistoryClassifier Left Right LeftEq RightEq h k ->
        SumHistoryCarrier Left Right k := by
  intro carrierH classifier
  cases classifier with
  | inl leftSame =>
      cases leftSame with
      | intro sourceH sourceRest =>
          cases sourceRest with
          | intro sourceK data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameSource =>
                      cases carrierH with
                      | inl leftCarrier =>
                          cases leftCarrier with
                          | intro carrierSource carrierData =>
                              cases carrierData with
                              | intro sameCarrier carrierLeft =>
                                  have sameSourceTags :
                                      hsame (BHist.e0 carrierSource) (BHist.e0 sourceH) :=
                                    hsame_trans (hsame_symm sameCarrier) sameH
                                  cases sameSourceTags
                                  exact Or.inl
                                    (Exists.intro sourceK
                                      (And.intro sameK
                                        (leftCert.carrier_respects_equiv sameSource
                                          carrierLeft)))
                      | inr rightCarrier =>
                          cases rightCarrier with
                          | intro carrierSource carrierData =>
                              cases carrierData with
                              | intro sameCarrier _ =>
                                  have impossible :
                                      hsame (BHist.e1 carrierSource) (BHist.e0 sourceH) :=
                                    hsame_trans (hsame_symm sameCarrier) sameH
                                  exact False.elim (not_hsame_e1_e0 impossible)
  | inr rightSame =>
      cases rightSame with
      | intro sourceH sourceRest =>
          cases sourceRest with
          | intro sourceK data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameSource =>
                      cases carrierH with
                      | inl leftCarrier =>
                          cases leftCarrier with
                          | intro carrierSource carrierData =>
                              cases carrierData with
                              | intro sameCarrier _ =>
                                  have impossible :
                                      hsame (BHist.e0 carrierSource) (BHist.e1 sourceH) :=
                                    hsame_trans (hsame_symm sameCarrier) sameH
                                  exact False.elim (not_hsame_e0_e1 impossible)
                      | inr rightCarrier =>
                          cases rightCarrier with
                          | intro carrierSource carrierData =>
                              cases carrierData with
                              | intro sameCarrier carrierRight =>
                                  have sameSourceTags :
                                      hsame (BHist.e1 carrierSource) (BHist.e1 sourceH) :=
                                    hsame_trans (hsame_symm sameCarrier) sameH
                                  cases sameSourceTags
                                  exact Or.inr
                                    (Exists.intro sourceK
                                      (And.intro sameK
                                        (rightCert.carrier_respects_equiv sameSource
                                          carrierRight)))

theorem SumHistoryClassifier_no_source_membership :
    SumHistoryClassifier (fun _ : BHist => False) (fun _ : BHist => False) hsame hsame
        (BHist.e0 BHist.Empty) (BHist.e0 BHist.Empty) ∧
      (SumHistoryCarrier (fun _ : BHist => False) (fun _ : BHist => False)
        (BHist.e0 BHist.Empty) → False) := by
  constructor
  · exact Or.inl
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (And.intro (hsame_refl (BHist.e0 BHist.Empty))
            (And.intro (hsame_refl (BHist.e0 BHist.Empty)) (hsame_refl BHist.Empty)))))
  · intro carrier
    cases carrier with
    | inl leftData =>
        cases leftData with
        | intro _ data =>
            exact data.right
    | inr rightData =>
        cases rightData with
        | intro _ data =>
            exact data.right

theorem SumHistoryClassifier_hsame_same_tag_exactness {Left Right : BHist → Prop} :
    (∀ {l l' : BHist},
      SumHistoryClassifier Left Right hsame hsame (BHist.e0 l) (BHist.e0 l') ↔
        hsame l l') ∧
      (∀ {r r' : BHist},
        SumHistoryClassifier Left Right hsame hsame (BHist.e1 r) (BHist.e1 r') ↔
          hsame r r') := by
  constructor
  · intro l l'
    constructor
    · intro classifier
      exact SumHistoryClassifier_left_hsame_inversion classifier
    · intro samePayload
      exact Or.inl
        (Exists.intro l
          (Exists.intro l'
            (And.intro (hsame_refl (BHist.e0 l))
              (And.intro (hsame_refl (BHist.e0 l')) samePayload))))
  · intro r r'
    constructor
    · intro classifier
      exact SumHistoryClassifier_right_hsame_inversion classifier
    · intro samePayload
      exact Or.inr
        (Exists.intro r
          (Exists.intro r'
            (And.intro (hsame_refl (BHist.e1 r))
              (And.intro (hsame_refl (BHist.e1 r')) samePayload))))

end BEDC.Derived.SumUp
