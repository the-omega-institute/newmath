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

  theorem SumHistoryClassifier_symm_from_nameCert
    {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq) {h k : BHist} :
    SumHistoryClassifier Left Right LeftEq RightEq h k →
      SumHistoryClassifier Left Right LeftEq RightEq k h := by
  intro classifier
  exact
    match classifier with
    | Or.inl ⟨l, l', sameH, sameK, sameLeft⟩ =>
        Or.inl ⟨l', l, sameK, sameH, leftCert.equiv_symm sameLeft⟩
    | Or.inr ⟨r, r', sameH, sameK, sameRight⟩ =>
        Or.inr ⟨r', r, sameK, sameH, rightCert.equiv_symm sameRight⟩

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

theorem SumHistoryClassifier_generic_same_tag_exactness
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop} :
    (∀ {l l' : BHist},
      SumHistoryClassifier Left Right LeftEq RightEq (BHist.e0 l) (BHist.e0 l') ↔
        ∃ a a' : BHist, hsame l a ∧ hsame l' a' ∧ LeftEq a a') ∧
      (∀ {r r' : BHist},
        SumHistoryClassifier Left Right LeftEq RightEq (BHist.e1 r) (BHist.e1 r') ↔
          ∃ b b' : BHist, hsame r b ∧ hsame r' b' ∧ RightEq b b') := by
  constructor
  · intro l l'
    constructor
    · intro classifier
      cases classifier with
      | inl leftData =>
          cases leftData with
          | intro a rest =>
              cases rest with
              | intro a' data =>
                  cases data with
                  | intro sameL rest =>
                      cases rest with
                      | intro sameL' relAA' =>
                          exact Exists.intro a
                            (Exists.intro a'
                              (And.intro (hsame_e0_iff.mp sameL)
                                (And.intro (hsame_e0_iff.mp sameL') relAA')))
      | inr rightData =>
          cases rightData with
          | intro b rest =>
              cases rest with
              | intro _ data =>
                  cases data with
                  | intro sameLeftRight _ =>
                      exact False.elim (not_hsame_e0_e1 sameLeftRight)
    · intro witness
      cases witness with
      | intro a rest =>
          cases rest with
          | intro a' data =>
              cases data with
              | intro sameL rest =>
                  cases rest with
                  | intro sameL' relAA' =>
                      exact Or.inl
                        (Exists.intro a
                          (Exists.intro a'
                            (And.intro (hsame_e0_congr sameL)
                              (And.intro (hsame_e0_congr sameL') relAA'))))
  · intro r r'
    constructor
    · intro classifier
      cases classifier with
      | inl leftData =>
          cases leftData with
          | intro a rest =>
              cases rest with
              | intro _ data =>
                  cases data with
                  | intro sameRightLeft _ =>
                      exact False.elim (not_hsame_e1_e0 sameRightLeft)
      | inr rightData =>
          cases rightData with
          | intro b rest =>
              cases rest with
              | intro b' data =>
                  cases data with
                  | intro sameR rest =>
                      cases rest with
                      | intro sameR' relBB' =>
                          exact Exists.intro b
                            (Exists.intro b'
                              (And.intro (hsame_e1_iff.mp sameR)
                                (And.intro (hsame_e1_iff.mp sameR') relBB')))
    · intro witness
      cases witness with
      | intro b rest =>
          cases rest with
          | intro b' data =>
              cases data with
              | intro sameR rest =>
                  cases rest with
                  | intro sameR' relBB' =>
                      exact Or.inr
                        (Exists.intro b
                          (Exists.intro b'
                            (And.intro (hsame_e1_congr sameR)
                              (And.intro (hsame_e1_congr sameR') relBB'))))

theorem SumHistoryClassifier_source_parameter_irrelevance
    {Left Right LeftAlt RightAlt : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    SumHistoryClassifier Left Right LeftEq RightEq h k ↔
      SumHistoryClassifier LeftAlt RightAlt LeftEq RightEq h k := by
  constructor
  · intro classifier
    cases classifier with
    | inl leftData =>
        cases leftData with
        | intro l rest =>
            cases rest with
            | intro l' data =>
                cases data with
                | intro sameH rest =>
                    cases rest with
                    | intro sameK sameLeft =>
                        exact Or.inl
                          (Exists.intro l
                            (Exists.intro l'
                              (And.intro sameH (And.intro sameK sameLeft))))
    | inr rightData =>
        cases rightData with
        | intro r rest =>
            cases rest with
            | intro r' data =>
                cases data with
                | intro sameH rest =>
                    cases rest with
                    | intro sameK sameRight =>
                        exact Or.inr
                          (Exists.intro r
                            (Exists.intro r'
                              (And.intro sameH (And.intro sameK sameRight))))
  · intro classifier
    cases classifier with
    | inl leftData =>
        cases leftData with
        | intro l rest =>
            cases rest with
            | intro l' data =>
                cases data with
                | intro sameH rest =>
                    cases rest with
                    | intro sameK sameLeft =>
                        exact Or.inl
                          (Exists.intro l
                            (Exists.intro l'
                              (And.intro sameH (And.intro sameK sameLeft))))
    | inr rightData =>
        cases rightData with
        | intro r rest =>
            cases rest with
            | intro r' data =>
                cases data with
                | intro sameH rest =>
                    cases rest with
                    | intro sameK sameRight =>
                        exact Or.inr
                          (Exists.intro r
                            (Exists.intro r'
                              (And.intro sameH (And.intro sameK sameRight))))

theorem SumHistoryClassifier_reverse_tag_separation {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k l r : BHist} :
    hsame h (BHist.e1 r) →
      hsame k (BHist.e0 l) →
        SumHistoryClassifier Left Right LeftEq RightEq h k → False := by
  intro sameHRight sameKLeft classifier
  cases classifier with
  | inl leftData =>
      cases leftData with
      | intro sourceH rest =>
          cases rest with
          | intro _sourceK data =>
              cases data with
              | intro sameHLeft _rest =>
                  exact not_hsame_e1_e0 (hsame_trans (hsame_symm sameHRight) sameHLeft)
  | inr rightData =>
      cases rightData with
      | intro _sourceH rest =>
          cases rest with
          | intro sourceK data =>
              cases data with
              | intro _sameH rest =>
                  cases rest with
                  | intro sameKRight _sameSource =>
                      exact not_hsame_e1_e0
                        (hsame_trans (hsame_symm sameKRight) sameKLeft)

end BEDC.Derived.SumUp
