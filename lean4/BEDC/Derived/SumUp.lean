import BEDC.FKernel.NameCert

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SumHistoryCarrier (Left Right : BHist → Prop) (h : BHist) : Prop :=
  (∃ l : BHist, hsame h (BHist.e0 l) ∧ Left l) ∨
    (∃ r : BHist, hsame h (BHist.e1 r) ∧ Right r)

theorem SumHistoryCarrier_hsame_transport {Left Right : BHist -> Prop} {h k : BHist} :
    hsame h k -> SumHistoryCarrier Left Right h -> SumHistoryCarrier Left Right k := by
  intro same carrier
  cases carrier with
  | inl leftData =>
      cases leftData with
      | intro leftHist data =>
          cases data with
          | intro sameTag leftCarrier =>
              exact Or.inl
                (Exists.intro leftHist
                  (And.intro (hsame_trans (hsame_symm same) sameTag) leftCarrier))
  | inr rightData =>
      cases rightData with
      | intro rightHist data =>
          cases data with
          | intro sameTag rightCarrier =>
              exact Or.inr
                (Exists.intro rightHist
                  (And.intro (hsame_trans (hsame_symm same) sameTag) rightCarrier))

def SumHistoryClassifier (_Left _Right : BHist → Prop)
    (LeftEq RightEq : BHist → BHist → Prop) (h k : BHist) : Prop :=
  (∃ l : BHist, ∃ l' : BHist,
    hsame h (BHist.e0 l) ∧ hsame k (BHist.e0 l') ∧ LeftEq l l') ∨
    (∃ r : BHist, ∃ r' : BHist,
      hsame h (BHist.e1 r) ∧ hsame k (BHist.e1 r') ∧ RightEq r r')

theorem SumHistoryClassifier_trans {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (left_trans : forall {a b c : BHist}, LeftEq a b -> LeftEq b c -> LeftEq a c)
    (right_trans : forall {a b c : BHist}, RightEq a b -> RightEq b c -> RightEq a c)
    {h k r : BHist} :
    SumHistoryClassifier Left Right LeftEq RightEq h k ->
      SumHistoryClassifier Left Right LeftEq RightEq k r ->
        SumHistoryClassifier Left Right LeftEq RightEq h r := by
  intro sameHK sameKR
  cases sameHK with
  | inl leftHK =>
      cases leftHK with
      | intro hLeft leftRest =>
          cases leftRest with
          | intro kLeft dataHK =>
              cases dataHK with
              | intro sameH restHK =>
                  cases restHK with
                  | intro sameKLeft sameLeftHK =>
                      cases sameKR with
                      | inl leftKR =>
                          cases leftKR with
                          | intro kLeft' leftRestKR =>
                              cases leftRestKR with
                              | intro rLeft dataKR =>
                                  cases dataKR with
                                  | intro sameKLeft' restKR =>
                                      cases restKR with
                                      | intro sameR sameLeftKR =>
                                          have sameMiddle :
                                              hsame (BHist.e0 kLeft) (BHist.e0 kLeft') :=
                                            hsame_trans (hsame_symm sameKLeft) sameKLeft'
                                          cases sameMiddle
                                          exact Or.inl
                                            (Exists.intro hLeft
                                              (Exists.intro rLeft
                                                (And.intro sameH
                                                  (And.intro sameR
                                                    (left_trans sameLeftHK sameLeftKR)))))
                      | inr rightKR =>
                          cases rightKR with
                          | intro kRight rightRestKR =>
                              cases rightRestKR with
                              | intro rRight dataKR =>
                                  cases dataKR with
                                  | intro sameKRight _ =>
                                      have impossible :
                                          hsame (BHist.e0 kLeft) (BHist.e1 kRight) :=
                                        hsame_trans (hsame_symm sameKLeft) sameKRight
                                      exact False.elim (not_hsame_e0_e1 impossible)
  | inr rightHK =>
      cases rightHK with
      | intro hRight rightRest =>
          cases rightRest with
          | intro kRight dataHK =>
              cases dataHK with
              | intro sameH restHK =>
                  cases restHK with
                  | intro sameKRight sameRightHK =>
                      cases sameKR with
                      | inl leftKR =>
                          cases leftKR with
                          | intro kLeft leftRestKR =>
                              cases leftRestKR with
                              | intro rLeft dataKR =>
                                  cases dataKR with
                                  | intro sameKLeft _ =>
                                      have impossible :
                                          hsame (BHist.e1 kRight) (BHist.e0 kLeft) :=
                                        hsame_trans (hsame_symm sameKRight) sameKLeft
                                      exact False.elim (not_hsame_e1_e0 impossible)
                      | inr rightKR =>
                          cases rightKR with
                          | intro kRight' rightRestKR =>
                              cases rightRestKR with
                              | intro rRight dataKR =>
                                  cases dataKR with
                                  | intro sameKRight' restKR =>
                                      cases restKR with
                                      | intro sameR sameRightKR =>
                                          have sameMiddle :
                                              hsame (BHist.e1 kRight) (BHist.e1 kRight') :=
                                            hsame_trans (hsame_symm sameKRight) sameKRight'
                                          cases sameMiddle
                                          exact Or.inr
                                            (Exists.intro hRight
                                              (Exists.intro rRight
                                                (And.intro sameH
                                                  (And.intro sameR
                                                    (right_trans sameRightHK sameRightKR)))))

theorem SumHistoryClassifier_hsame_symm {Left Right : BHist -> Prop} {h k : BHist} :
    SumHistoryClassifier Left Right hsame hsame h k ->
      SumHistoryClassifier Left Right hsame hsame k h := by
  intro classifier
  cases classifier with
  | inl leftData =>
      cases leftData with
      | intro l leftRest =>
          cases leftRest with
          | intro l' data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameLeft =>
                      exact Or.inl
                        (Exists.intro l'
                          (Exists.intro l
                            (And.intro sameK (And.intro sameH (hsame_symm sameLeft)))))
  | inr rightData =>
      cases rightData with
      | intro r rightRest =>
          cases rightRest with
          | intro r' data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameRight =>
                      exact Or.inr
                        (Exists.intro r'
                          (Exists.intro r
                            (And.intro sameK (And.intro sameH (hsame_symm sameRight)))))

theorem SumHistoryClassifier_mixed_tags_absurd {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k l r : BHist} :
    hsame h (BHist.e0 l) → hsame k (BHist.e1 r) →
      SumHistoryClassifier Left Right LeftEq RightEq h k → False := by
  intro sameHLeft sameKRight classifier
  cases classifier with
  | inl leftData =>
      cases leftData with
      | intro _ sourceRest =>
          cases sourceRest with
          | intro targetLeft data =>
              cases data with
              | intro _ rest =>
                  cases rest with
                  | intro sameKLeft _ =>
                      exact not_hsame_e0_e1 (hsame_trans (hsame_symm sameKLeft) sameKRight)
  | inr rightData =>
      cases rightData with
      | intro sourceRight sourceRest =>
          cases sourceRest with
          | intro _ data =>
              cases data with
              | intro sameHRight _ =>
                  exact not_hsame_e0_e1 (hsame_trans (hsame_symm sameHLeft) sameHRight)

theorem SumHistoryClassifier_left_right_absurd {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k l r : BHist} :
    hsame h (BHist.e0 l) →
      hsame k (BHist.e1 r) →
        SumHistoryClassifier Left Right LeftEq RightEq h k →
          False := by
  intro hLeft kRight classified
  cases classified with
  | inl leftData =>
      cases leftData with
      | intro source leftRest =>
          cases leftRest with
          | intro target data =>
              cases data with
              | intro _ rest =>
                  cases rest with
                  | intro kLeft _ =>
                      have impossible : hsame (BHist.e0 target) (BHist.e1 r) :=
                        hsame_trans (hsame_symm kLeft) kRight
                      exact not_hsame_e0_e1 impossible
  | inr rightData =>
      cases rightData with
      | intro source rightRest =>
          cases rightRest with
          | intro _ data =>
              cases data with
              | intro hRight _ =>
                  have impossible : hsame (BHist.e0 l) (BHist.e1 source) :=
                    hsame_trans (hsame_symm hLeft) hRight
                  exact not_hsame_e0_e1 impossible

theorem sum_history_semantic_name_certificate {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq) :
    SemanticNameCert (SumHistoryCarrier Left Right) (SumHistoryCarrier Left Right)
      (SumHistoryCarrier Left Right) (SumHistoryClassifier Left Right LeftEq RightEq) := by
  exact {
    core := {
      carrier_inhabited := by
        cases leftCert.carrier_inhabited with
        | intro l leftCarrier =>
            exact Exists.intro (BHist.e0 l)
              (Or.inl (Exists.intro l (And.intro (hsame_refl (BHist.e0 l)) leftCarrier)))
      equiv_refl := by
        intro h carrier
        cases carrier with
        | inl leftData =>
            cases leftData with
            | intro l data =>
                cases data with
                | intro sameTag leftCarrier =>
                    exact Or.inl
                      (Exists.intro l
                        (Exists.intro l
                          (And.intro sameTag
                            (And.intro sameTag (leftCert.equiv_refl leftCarrier)))))
        | inr rightData =>
            cases rightData with
            | intro r data =>
                cases data with
                | intro sameTag rightCarrier =>
                    exact Or.inr
                      (Exists.intro r
                        (Exists.intro r
                          (And.intro sameTag
                            (And.intro sameTag (rightCert.equiv_refl rightCarrier)))))
      equiv_symm := by
        intro h k same
        cases same with
        | inl leftData =>
            cases leftData with
            | intro l leftRest =>
                cases leftRest with
                | intro l' data =>
                    cases data with
                    | intro sameH rest =>
                        cases rest with
                        | intro sameK sameLeft =>
                            exact Or.inl
                              (Exists.intro l'
                                (Exists.intro l
                                  (And.intro sameK
                                    (And.intro sameH (leftCert.equiv_symm sameLeft)))))
        | inr rightData =>
            cases rightData with
            | intro r rightRest =>
                cases rightRest with
                | intro r' data =>
                    cases data with
                    | intro sameH rest =>
                        cases rest with
                        | intro sameK sameRight =>
                            exact Or.inr
                              (Exists.intro r'
                                (Exists.intro r
                                  (And.intro sameK
                                    (And.intro sameH (rightCert.equiv_symm sameRight)))))
      equiv_trans := by
        intro h k r sameHK sameKR
        cases sameHK with
        | inl leftHK =>
            cases leftHK with
            | intro hLeft leftRest =>
                cases leftRest with
                | intro kLeft dataHK =>
                    cases dataHK with
                    | intro sameH restHK =>
                        cases restHK with
                        | intro sameKLeft sameLeftHK =>
                            cases sameKR with
                            | inl leftKR =>
                                cases leftKR with
                                | intro kLeft' leftRestKR =>
                                    cases leftRestKR with
                                    | intro rLeft dataKR =>
                                        cases dataKR with
                                        | intro sameKLeft' restKR =>
                                            cases restKR with
                                            | intro sameR sameLeftKR =>
                                                have sameMiddle :
                                                    hsame (BHist.e0 kLeft)
                                                      (BHist.e0 kLeft') :=
                                                  hsame_trans (hsame_symm sameKLeft)
                                                    sameKLeft'
                                                cases sameMiddle
                                                exact Or.inl
                                                  (Exists.intro hLeft
                                                    (Exists.intro rLeft
                                                      (And.intro sameH
                                                        (And.intro sameR
                                                          (leftCert.equiv_trans sameLeftHK
                                                            sameLeftKR)))))
                            | inr rightKR =>
                                cases rightKR with
                                | intro kRight rightRestKR =>
                                    cases rightRestKR with
                                    | intro rRight dataKR =>
                                        cases dataKR with
                                        | intro sameKRight _ =>
                                            have impossible :
                                                hsame (BHist.e0 kLeft) (BHist.e1 kRight) :=
                                              hsame_trans (hsame_symm sameKLeft) sameKRight
                                            exact False.elim (not_hsame_e0_e1 impossible)
        | inr rightHK =>
            cases rightHK with
            | intro hRight rightRest =>
                cases rightRest with
                | intro kRight dataHK =>
                    cases dataHK with
                    | intro sameH restHK =>
                        cases restHK with
                        | intro sameKRight sameRightHK =>
                            cases sameKR with
                            | inl leftKR =>
                                cases leftKR with
                                | intro kLeft leftRestKR =>
                                    cases leftRestKR with
                                    | intro rLeft dataKR =>
                                        cases dataKR with
                                        | intro sameKLeft _ =>
                                            have impossible :
                                                hsame (BHist.e1 kRight) (BHist.e0 kLeft) :=
                                              hsame_trans (hsame_symm sameKRight) sameKLeft
                                            exact False.elim (not_hsame_e1_e0 impossible)
                            | inr rightKR =>
                                cases rightKR with
                                | intro kRight' rightRestKR =>
                                    cases rightRestKR with
                                    | intro rRight dataKR =>
                                        cases dataKR with
                                        | intro sameKRight' restKR =>
                                            cases restKR with
                                            | intro sameR sameRightKR =>
                                                have sameMiddle :
                                                    hsame (BHist.e1 kRight)
                                                      (BHist.e1 kRight') :=
                                                  hsame_trans (hsame_symm sameKRight)
                                                    sameKRight'
                                                cases sameMiddle
                                                exact Or.inr
                                                  (Exists.intro hRight
                                                    (Exists.intro rRight
                                                      (And.intro sameH
                                                        (And.intro sameR
                                                          (rightCert.equiv_trans sameRightHK
                                                            sameRightKR)))))
      carrier_respects_equiv := by
        intro h k same carrierH
        cases same with
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
                                            hsame (BHist.e0 carrierSource)
                                              (BHist.e0 sourceH) :=
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
                                            hsame (BHist.e1 carrierSource)
                                              (BHist.e0 sourceH) :=
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
                                            hsame (BHist.e0 carrierSource)
                                              (BHist.e1 sourceH) :=
                                          hsame_trans (hsame_symm sameCarrier) sameH
                                        exact False.elim (not_hsame_e0_e1 impossible)
                            | inr rightCarrier =>
                                cases rightCarrier with
                                | intro carrierSource carrierData =>
                                    cases carrierData with
                                    | intro sameCarrier carrierRight =>
                                        have sameSourceTags :
                                            hsame (BHist.e1 carrierSource)
                                              (BHist.e1 sourceH) :=
                                          hsame_trans (hsame_symm sameCarrier) sameH
                                        cases sameSourceTags
                                        exact Or.inr
                                          (Exists.intro sourceK
                                            (And.intro sameK
                                              (rightCert.carrier_respects_equiv sameSource
                                                carrierRight)))
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

def SumCarrier (A B : Type) := Sum A B

def SumClassifierSpec {A B : Type} (sameA : A → A → Prop) (sameB : B → B → Prop) :
    SumCarrier A B → SumCarrier A B → Prop
  | Sum.inl a, Sum.inl a' => sameA a a'
  | Sum.inr b, Sum.inr b' => sameB b b'
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

theorem sum_stability_certificate_fields {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} (reflA : ∀ a, sameA a a) (reflB : ∀ b, sameB b b)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c)
    (transB : ∀ {a b c}, sameB a b → sameB b c → sameB a c) :
    (∀ a : A, SumClassifierSpec sameA sameB (Sum.inl a) (Sum.inl a)) ∧
      (∀ b : B, SumClassifierSpec sameA sameB (Sum.inr b) (Sum.inr b)) ∧
      (∀ {x y z : SumCarrier A B},
        SumClassifierSpec sameA sameB x y →
          SumClassifierSpec sameA sameB y z →
            SumClassifierSpec sameA sameB x z) ∧
      (∀ (a : A) (b : B), SumClassifierSpec sameA sameB (Sum.inl a) (Sum.inr b) →
        False) ∧
      (∀ (a : A) (b : B), SumClassifierSpec sameA sameB (Sum.inr b) (Sum.inl a) →
        False) := by
  constructor
  · intro a
    exact reflA a
  · constructor
    · intro b
      exact reflB b
    · constructor
      · intro x y z hxy hyz
        cases x with
        | inl _ =>
            cases y with
            | inl _ =>
                cases z with
                | inl _ =>
                    exact transA hxy hyz
                | inr _ =>
                    exact hyz
            | inr _ =>
                cases hxy
        | inr _ =>
            cases y with
            | inl _ =>
                cases hxy
            | inr _ =>
                cases z with
                | inl _ =>
                    exact hyz
                | inr _ =>
                    exact transB hxy hyz
      · constructor
        · intro a b h
          exact h
        · intro a b h
          exact h

theorem SumClassifierSpec_trans {A B : Type} {RelA : A → A → Prop}
    {RelB : B → B → Prop}
    (relA_trans : ∀ {a b c : A}, RelA a b → RelA b c → RelA a c)
    (relB_trans : ∀ {a b c : B}, RelB a b → RelB b c → RelB a c) :
    ∀ {x y z : Sum A B},
      SumClassifierSpec RelA RelB x y →
        SumClassifierSpec RelA RelB y z →
          SumClassifierSpec RelA RelB x z := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;> simp [SumClassifierSpec] at *
  · exact relA_trans hxy hyz
  · exact relB_trans hxy hyz

theorem sum_classifier_inversion {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} {x y : Sum A B} :
    SumClassifierSpec sameA sameB x y →
      (∃ a : A, ∃ a' : A, x = Sum.inl a ∧ y = Sum.inl a' ∧ sameA a a') ∨
        (∃ b : B, ∃ b' : B, x = Sum.inr b ∧ y = Sum.inr b' ∧ sameB b b') := by
  intro h
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          exact Or.inl ⟨a, a', rfl, rfl, h⟩
      | inr b =>
          cases h
  | inr b =>
      cases y with
      | inl a =>
          cases h
      | inr b' =>
          exact Or.inr ⟨b, b', rfl, rfl, h⟩

end BEDC.Derived.SumUp
