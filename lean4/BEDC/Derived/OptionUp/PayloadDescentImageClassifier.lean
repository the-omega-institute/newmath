import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def TaggedOptionPayloadDescentImageClassifier (S T : BHist → Prop)
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) (k k' : BHist) : Prop :=
  ∃ h h' : BHist,
    TaggedOptionHistoryClassifier S RelS h h' ∧ TaggedOptionMapRel S T delta h k ∧
      TaggedOptionMapRel S T delta h' k'

theorem TaggedOptionPayloadDescentImageClassifier_branch_exactness {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ↔
      (hsame k BHist.Empty ∧ hsame k' BHist.Empty) ∨
        ∃ a b : BHist,
          S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
            hsame k (BHist.e1 (delta.map a)) ∧ hsame k' (BHist.e1 (delta.map b)) := by
  constructor
  · intro image
    cases image with
    | intro h image =>
        cases image with
        | intro h' image =>
            cases image with
            | intro sourceClass maps =>
                cases maps with
                | intro mapH mapH' =>
                    cases sourceClass with
                    | inl absent =>
                        cases mapH with
                        | inl mapAbsent =>
                            cases mapH' with
                            | inl mapAbsent' =>
                                exact Or.inl (And.intro mapAbsent.right mapAbsent'.right)
                            | inr mapPresent' =>
                                cases mapPresent' with
                                | intro _a data =>
                                    exact False.elim
                                      (not_hsame_emp_e1
                                        (hsame_trans (hsame_symm absent.right)
                                          data.right.right.left))
                        | inr mapPresent =>
                            cases mapPresent with
                            | intro _a data =>
                                exact False.elim
                                  (not_hsame_emp_e1
                                    (hsame_trans (hsame_symm absent.left)
                                      data.right.right.left))
                    | inr present =>
                        cases present with
                        | intro a present =>
                            cases present with
                            | intro b data =>
                                cases mapH with
                                | inl mapAbsent =>
                                    exact False.elim
                                      (not_hsame_emp_e1
                                        (hsame_trans (hsame_symm mapAbsent.left)
                                          data.right.right.left))
                                | inr mapPresent =>
                                    cases mapPresent with
                                    | intro a0 dataA0 =>
                                        cases mapH' with
                                        | inl mapAbsent' =>
                                            exact False.elim
                                              (not_hsame_emp_e1
                                                (hsame_trans (hsame_symm mapAbsent'.left)
                                                  data.right.right.right.left))
                                        | inr mapPresent' =>
                                            cases mapPresent' with
                                            | intro b0 dataB0 =>
                                                have sameA0A : hsame a0 a :=
                                                  hsame_e1_iff.mp
                                                    (hsame_trans
                                                      (hsame_symm dataA0.right.right.left)
                                                      data.right.right.left)
                                                have sameBB0 : hsame b b0 :=
                                                  hsame_e1_iff.mp
                                                    (hsame_trans
                                                      (hsame_symm data.right.right.right.left)
                                                      dataB0.right.right.left)
                                                have relA0A : RelS a0 a :=
                                                  source_hsame dataA0.left data.left sameA0A
                                                have relBB0 : RelS b b0 :=
                                                  source_hsame data.right.left dataB0.left sameBB0
                                                have relA0B : RelS a0 b :=
                                                  NameCert.equiv_trans cert relA0A
                                                    data.right.right.right.right
                                                have relA0B0 : RelS a0 b0 :=
                                                  NameCert.equiv_trans cert relA0B relBB0
                                                exact Or.inr
                                                  (Exists.intro a0
                                                    (Exists.intro b0
                                                      (And.intro dataA0.left
                                                        (And.intro dataB0.left
                                                          (And.intro relA0B0
                                                            (And.intro dataA0.right.left
                                                              (And.intro dataB0.right.left
                                                                (And.intro
                                                                  dataA0.right.right.right
                                                                  dataB0.right.right.right))))))))
  · intro branch
    cases branch with
    | inl absent =>
        exact ⟨BHist.Empty, BHist.Empty,
          Or.inl (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)),
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.left),
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.right)⟩
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                exact ⟨BHist.e1 a, BHist.e1 b,
                  Or.inr
                    ⟨a, b, data.left, data.right.left, hsame_refl (BHist.e1 a),
                      hsame_refl (BHist.e1 b), data.right.right.left⟩,
                  Or.inr
                    ⟨a, data.left, data.right.right.right.left,
                      hsame_refl (BHist.e1 a), data.right.right.right.right.right.left⟩,
                  Or.inr
                    ⟨b, data.right.left, data.right.right.right.right.left,
                      hsame_refl (BHist.e1 b), data.right.right.right.right.right.right⟩⟩

theorem TaggedOptionPayloadDescentImageClassifier_target_classifier_closure {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      TaggedOptionHistoryClassifier T RelT k k' := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  cases branch with
  | inl absent =>
      exact Or.inl absent
  | inr present =>
      cases present with
      | intro a present =>
          cases present with
          | intro b data =>
              exact Or.inr
                ⟨delta.map a, delta.map b, data.right.right.right.left,
                  data.right.right.right.right.left,
                  data.right.right.right.right.right.left,
                  data.right.right.right.right.right.right,
                  delta.respects data.right.right.left⟩

theorem TaggedOptionPayloadDescentImageClassifier_right_visible_branch_inversion
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      (hsame k' BHist.Empty → hsame k BHist.Empty) ∧
        (∀ {a : BHist}, T a → hsame k' (BHist.e1 a) →
          ∃ b c : BHist,
            S b ∧ S c ∧ RelS b c ∧ T (delta.map b) ∧ T (delta.map c) ∧
              hsame a (delta.map c) ∧ hsame k (BHist.e1 (delta.map b))) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  constructor
  · intro sameRightEmpty
    cases branch with
    | inl absent =>
        exact absent.left
    | inr present =>
        cases present with
        | intro b present =>
            cases present with
            | intro c data =>
                exact False.elim
                  (not_hsame_emp_e1
                    (hsame_trans (hsame_symm sameRightEmpty)
                      data.right.right.right.right.right.right))
  · intro a _targetA visibleRight
    cases branch with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) visibleRight))
    | inr present =>
        cases present with
        | intro b present =>
            cases present with
            | intro c data =>
                have payloadSame : hsame a (delta.map c) :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm visibleRight)
                      data.right.right.right.right.right.right)
                exact Exists.intro b
                  (Exists.intro c
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro payloadSame
                                data.right.right.right.right.right.left)))))))

theorem TaggedOptionPayloadDescentImageClassifier_left_visible_branch_inversion
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      (hsame k BHist.Empty → hsame k' BHist.Empty) ∧
        (∀ {a : BHist}, T a → hsame k (BHist.e1 a) →
          ∃ b c : BHist,
            S b ∧ S c ∧ RelS b c ∧ T (delta.map b) ∧ T (delta.map c) ∧
              hsame a (delta.map b) ∧ hsame k' (BHist.e1 (delta.map c))) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  constructor
  · intro sameLeftEmpty
    cases branch with
    | inl absent =>
        exact absent.right
    | inr present =>
        cases present with
        | intro b present =>
            cases present with
            | intro c data =>
                exact False.elim
                  (not_hsame_emp_e1
                    (hsame_trans (hsame_symm sameLeftEmpty)
                      data.right.right.right.right.right.left))
  · intro a _targetA visibleLeft
    cases branch with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) visibleLeft))
    | inr present =>
        cases present with
        | intro b present =>
            cases present with
            | intro c data =>
                have payloadSame : hsame a (delta.map b) :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm visibleLeft)
                      data.right.right.right.right.right.left)
                exact Exists.intro b
                  (Exists.intro c
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro payloadSame
                                data.right.right.right.right.right.right)))))))

theorem TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' u v : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      T u →
        T v →
          hsame k (BHist.e1 u) →
            hsame k' (BHist.e1 v) →
              ∃ a : BHist,
                ∃ b : BHist,
                  S a ∧
                    S b ∧
                      RelS a b ∧
                        T (delta.map a) ∧
                          T (delta.map b) ∧
                            hsame u (delta.map a) ∧ hsame v (delta.map b) := by
  intro image _visibleU _visibleV sameK sameK'
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp image
  cases branch with
  | inl absent =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameK))
  | inr present =>
      cases present with
      | intro a present =>
          cases present with
          | intro b data =>
              have sameU : hsame u (delta.map a) :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm sameK) data.right.right.right.right.right.left)
              have sameV : hsame v (delta.map b) :=
                hsame_e1_iff.mp
                  (hsame_trans (hsame_symm sameK')
                    data.right.right.right.right.right.right)
              exact Exists.intro a
                (Exists.intro b
                  (And.intro data.left
                    (And.intro data.right.left
                      (And.intro data.right.right.left
                        (And.intro data.right.right.right.left
                          (And.intro data.right.right.right.right.left
                            (And.intro sameU sameV)))))))

theorem TaggedOptionPayloadDescentImageClassifier_pair_readback_single_valued
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      ((hsame k BHist.Empty ∧ hsame k' BHist.Empty ∧
          ((∃ a b : BHist,
            S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
              hsame k (BHist.e1 (delta.map a)) ∧
                hsame k' (BHist.e1 (delta.map b))) → False)) ∨
        (∃ a b : BHist,
          S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
            hsame k (BHist.e1 (delta.map a)) ∧
              hsame k' (BHist.e1 (delta.map b)) ∧
                (hsame k BHist.Empty → False) ∧ (hsame k' BHist.Empty → False) ∧
                  (∀ a' b' : BHist,
                    S a' → S b' → RelS a' b' → T (delta.map a') →
                      T (delta.map b') → hsame k (BHist.e1 (delta.map a')) →
                        hsame k' (BHist.e1 (delta.map b')) →
                          hsame (delta.map a) (delta.map a') ∧
                            hsame (delta.map b) (delta.map b')))) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  cases branch with
  | inl absent =>
      exact Or.inl
        (And.intro absent.left
          (And.intro absent.right
            (by
              intro present
              cases present with
              | intro a present =>
                  cases present with
                  | intro b data =>
                      exact not_hsame_emp_e1
                        (hsame_trans (hsame_symm absent.left)
                          data.right.right.right.right.right.left))))
  | inr present =>
      cases present with
      | intro a present =>
          cases present with
          | intro b data =>
              have notLeftEmpty : hsame k BHist.Empty → False := by
                intro sameEmpty
                exact not_hsame_emp_e1
                  (hsame_trans (hsame_symm sameEmpty)
                    data.right.right.right.right.right.left)
              have notRightEmpty : hsame k' BHist.Empty → False := by
                intro sameEmpty
                exact not_hsame_emp_e1
                  (hsame_trans (hsame_symm sameEmpty)
                    data.right.right.right.right.right.right)
              have unique :
                  ∀ a' b' : BHist,
                    S a' → S b' → RelS a' b' → T (delta.map a') →
                      T (delta.map b') → hsame k (BHist.e1 (delta.map a')) →
                        hsame k' (BHist.e1 (delta.map b')) →
                          hsame (delta.map a) (delta.map a') ∧
                            hsame (delta.map b) (delta.map b') := by
                intro a' b' _sourceA' _sourceB' _relA'B' _targetA' _targetB'
                  sameLeft sameRight
                constructor
                · exact hsame_e1_iff.mp
                    (hsame_trans (hsame_symm data.right.right.right.right.right.left)
                      sameLeft)
                · exact hsame_e1_iff.mp
                    (hsame_trans (hsame_symm data.right.right.right.right.right.right)
                      sameRight)
              exact Or.inr
                (Exists.intro a
                  (Exists.intro b
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                (And.intro data.right.right.right.right.right.right
                                  (And.intro notLeftEmpty
                                    (And.intro notRightEmpty unique)))))))))))

theorem TaggedOptionPayloadDescentImageClassifier_certificate
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      TaggedOptionPayloadDescentImageCarrier S T delta k ∧
        TaggedOptionPayloadDescentImageCarrier S T delta k' ∧
          TaggedOptionHistoryClassifier T RelT k k' := by
  intro image
  cases image with
  | intro h image =>
      cases image with
      | intro h' imageData =>
          cases imageData with
          | intro sourceClass maps =>
              cases maps with
              | intro mapH mapH' =>
                  have sourceCarriers :
                      TaggedOptionHistoryCarrier S h ∧ TaggedOptionHistoryCarrier S h' := by
                    cases sourceClass with
                    | inl absent =>
                        constructor
                        · exact Or.inl absent.left
                        · exact Or.inl absent.right
                    | inr present =>
                        cases present with
                        | intro a present =>
                            cases present with
                            | intro b data =>
                                constructor
                                · exact Or.inr
                                    (Exists.intro a
                                      (And.intro data.left
                                        data.right.right.left))
                                · exact Or.inr
                                    (Exists.intro b
                                      (And.intro data.right.left
                                        data.right.right.right.left))
                  exact And.intro
                    (Exists.intro h (And.intro sourceCarriers.left mapH))
                    (And.intro
                      (Exists.intro h' (And.intro sourceCarriers.right mapH'))
                      (TaggedOptionMapRel_preserves_classification delta cert source_hsame
                        sourceClass mapH mapH'))

theorem TaggedOptionPayloadDescentImageClassifier_self_exactness
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k ↔
      TaggedOptionPayloadDescentImageCarrier S T delta k := by
  constructor
  · intro image
    have branch :=
      (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
        image
    apply (TaggedOptionPayloadDescentImageCarrier_branch_exactness delta).mpr
    cases branch with
    | inl absent =>
        exact Or.inl absent.left
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro _b data =>
                exact Or.inr
                  (Exists.intro a
                    (And.intro data.left
                      (And.intro data.right.right.right.left
                        data.right.right.right.right.right.left)))
  · intro image
    have branch := (TaggedOptionPayloadDescentImageCarrier_branch_exactness delta).mp image
    apply (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mpr
    cases branch with
    | inl absent =>
        exact Or.inl (And.intro absent absent)
    | inr present =>
        cases present with
        | intro a data =>
            exact Or.inr
              (Exists.intro a
                (Exists.intro a
                  (And.intro data.left
                    (And.intro data.left
                      (And.intro (NameCert.equiv_refl cert data.left)
                        (And.intro data.right.left
                          (And.intro data.right.left
                            (And.intro data.right.right data.right.right))))))))

def TaggedOptionPayloadDescentReflectsSource (S : BHist → Prop)
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) : Prop :=
  ∀ a b : BHist, S a → S b → hsame (delta.map a) (delta.map b) → RelS a b

theorem TaggedOptionPayloadDescentImageClassifier_reflective_transitivity
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {k l m : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k l →
      TaggedOptionPayloadDescentImageClassifier S T delta l m →
        TaggedOptionPayloadDescentImageClassifier S T delta k m := by
  intro left right
  have exactLeft :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp left
  have exactRight :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp right
  apply
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mpr
  cases exactLeft with
  | inl absentLeft =>
      cases exactRight with
      | inl absentRight =>
          exact Or.inl (And.intro absentLeft.left absentRight.right)
      | inr presentRight =>
          cases presentRight with
          | intro _c presentRight =>
              cases presentRight with
              | intro _d dataRight =>
                  exact False.elim
                    (not_hsame_emp_e1
                      (hsame_trans (hsame_symm absentLeft.right)
                        dataRight.right.right.right.right.right.left))
  | inr presentLeft =>
      cases presentLeft with
      | intro a presentLeft =>
          cases presentLeft with
          | intro b dataLeft =>
              cases exactRight with
              | inl absentRight =>
                  exact False.elim
                    (not_hsame_e1_empty
                      (hsame_trans
                        (hsame_symm dataLeft.right.right.right.right.right.right)
                        absentRight.left))
              | inr presentRight =>
                  cases presentRight with
                  | intro c presentRight =>
                      cases presentRight with
                      | intro d dataRight =>
                          have sameBC : hsame (delta.map b) (delta.map c) :=
                            hsame_e1_iff.mp
                              (hsame_trans
                                (hsame_symm dataLeft.right.right.right.right.right.right)
                                dataRight.right.right.right.right.right.left)
                          have relBC : RelS b c :=
                            reflects b c dataLeft.right.left dataRight.left sameBC
                          have relAC : RelS a c :=
                            NameCert.equiv_trans cert dataLeft.right.right.left relBC
                          have relAD : RelS a d :=
                            NameCert.equiv_trans cert relAC dataRight.right.right.left
                          exact Or.inr
                            (Exists.intro a
                              (Exists.intro d
                                (And.intro dataLeft.left
                                  (And.intro dataRight.right.left
                                    (And.intro relAD
                                      (And.intro dataLeft.right.right.right.left
                                        (And.intro dataRight.right.right.right.right.left
                                          (And.intro dataLeft.right.right.right.right.right.left
                                            dataRight.right.right.right.right.right.right))))))))

theorem TaggedOptionPayloadDescentImageClassifier_hsame_transport {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      hsame k u →
        hsame k' u' →
          TaggedOptionPayloadDescentImageClassifier S T delta u u' := by
  intro image sameLeft sameRight
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  apply
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mpr
  cases branch with
  | inl absent =>
      exact Or.inl
        (And.intro (hsame_trans (hsame_symm sameLeft) absent.left)
          (hsame_trans (hsame_symm sameRight) absent.right))
  | inr present =>
      cases present with
      | intro a present =>
          cases present with
          | intro b data =>
              exact Or.inr
                (Exists.intro a
                  (Exists.intro b
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro
                                (hsame_trans (hsame_symm sameLeft)
                                  data.right.right.right.right.right.left)
                                (hsame_trans (hsame_symm sameRight)
                                  data.right.right.right.right.right.right)))))))))

end BEDC.Derived.OptionUp
