import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_nonempty_present_pair_inversion
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
      ((hsame k BHist.Empty -> False) ->
        exists a b : BHist,
          S a /\ S b /\ RelS a b /\ T (delta.map a) /\ T (delta.map b) /\
            hsame k (BHist.e1 (delta.map a)) /\
              hsame k' (BHist.e1 (delta.map b))) /\
        ((hsame k' BHist.Empty -> False) ->
          exists a b : BHist,
            S a /\ S b /\ RelS a b /\ T (delta.map a) /\ T (delta.map b) /\
              hsame k (BHist.e1 (delta.map a)) /\
                hsame k' (BHist.e1 (delta.map b))) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  constructor
  · intro notLeftEmpty
    cases branch with
    | inl absent =>
        exact False.elim (notLeftEmpty absent.left)
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                exact Exists.intro a
                  (Exists.intro b
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right)))))))
  · intro notRightEmpty
    cases branch with
    | inl absent =>
        exact False.elim (notRightEmpty absent.right)
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                exact Exists.intro a
                  (Exists.intro b
                    (And.intro data.left
                      (And.intro data.right.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right)))))))

theorem TaggedOptionPayloadDescentImageClassifier_reflective_transitive_visible_pair_coherence
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {k l m u v u' v' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k l ->
      TaggedOptionPayloadDescentImageClassifier S T delta l m ->
        T u ->
          T v ->
            hsame k (BHist.e1 u) ->
              hsame m (BHist.e1 v) ->
                T u' ->
                  T v' ->
                    hsame k (BHist.e1 u') ->
                      hsame m (BHist.e1 v') ->
                        exists a b : BHist,
                          S a /\ S b /\ RelS a b /\ T (delta.map a) /\
                            T (delta.map b) /\ hsame u (delta.map a) /\
                              hsame v (delta.map b) /\ hsame u' (delta.map a) /\
                                hsame v' (delta.map b) := by
  intro imageKL imageLM targetU targetV sameKU sameMV targetU' targetV' sameKU' sameMV'
  have imageKM :=
    TaggedOptionPayloadDescentImageClassifier_reflective_transitivity
      delta cert source_hsame reflects imageKL imageLM
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
      delta cert source_hsame imageKM targetU targetV sameKU sameMV
  cases readback with
  | intro a readback =>
      cases readback with
      | intro b data =>
          have sameU'U : hsame u' u :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameKU') sameKU)
          have sameV'V : hsame v' v :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameMV') sameMV)
          exact Exists.intro a
            (Exists.intro b
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.right.right.left
                    (And.intro data.right.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left
                          (And.intro data.right.right.right.right.right.right
                            (And.intro
                              (hsame_trans sameU'U
                                data.right.right.right.right.right.left)
                              (hsame_trans sameV'V
                                data.right.right.right.right.right.right))))))))))

theorem TaggedOptionPayloadDescentImageClassifier_transported_visible_payload_pair_coherence
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    {k k' u u' x y x' y' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
      hsame k u ->
        hsame k' u' ->
          T x ->
            T y ->
              hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) ->
                  T x' ->
                    T y' ->
                      hsame u (BHist.e1 x') ->
                        hsame u' (BHist.e1 y') ->
                          exists a b : BHist,
                            S a /\ S b /\ RelS a b /\ T (delta.map a) /\
                              T (delta.map b) /\ hsame x (delta.map a) /\
                                hsame y (delta.map b) /\ hsame x' (delta.map a) /\
                                  hsame y' (delta.map b) := by
  intro image sameLeft sameRight targetX targetY sameUX sameU'Y targetX' targetY'
    sameUX' sameU'Y'
  have transported :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      delta cert source_hsame image sameLeft sameRight
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
      delta cert source_hsame transported targetX targetY sameUX sameU'Y
  cases readback with
  | intro a readback =>
      cases readback with
      | intro b data =>
          have sameX'X : hsame x' x :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameUX') sameUX)
          have sameY'Y : hsame y' y :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm sameU'Y') sameU'Y)
          exact Exists.intro a
            (Exists.intro b
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.right.right.left
                    (And.intro data.right.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left
                          (And.intro data.right.right.right.right.right.right
                            (And.intro
                              (hsame_trans sameX'X
                                data.right.right.right.right.right.left)
                              (hsame_trans sameY'Y
                                data.right.right.right.right.right.right))))))))))

theorem TaggedOptionPayloadDescentImageClassifier_reflective_transitive_transport_visible_target_payload_classification
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {k l m p q u v : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k l ->
      TaggedOptionPayloadDescentImageClassifier S T delta l m ->
        hsame k p ->
          hsame m q ->
            T u ->
              T v ->
                hsame p (BHist.e1 u) ->
                  hsame q (BHist.e1 v) ->
                    RelT u v := by
  intro imageKL imageLM sameKP sameMQ targetU targetV samePU sameQV
  have imageKM :=
    TaggedOptionPayloadDescentImageClassifier_reflective_transitivity
      delta certS source_hsame reflects imageKL imageLM
  have sameKU : hsame k (BHist.e1 u) := hsame_trans sameKP samePU
  have sameMV : hsame m (BHist.e1 v) := hsame_trans sameMQ sameQV
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
      delta certS source_hsame imageKM targetU targetV sameKU sameMV
  cases readback with
  | intro a readback =>
      cases readback with
      | intro b data =>
          have relImage : RelT (delta.map a) (delta.map b) :=
            delta.respects data.right.right.left
          have relLeft : RelT u (delta.map a) :=
            target_hsame targetU data.right.right.right.left
              data.right.right.right.right.right.left
          have relRight : RelT (delta.map b) v :=
            target_hsame data.right.right.right.right.left targetV
              (hsame_symm data.right.right.right.right.right.right)
          exact NameCert.equiv_trans certT (NameCert.equiv_trans certT relLeft relImage) relRight

theorem TaggedOptionPayloadDescentImageClassifier_reflective_transitive_normalized_visible_payload_single_valued
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta)
    {k l m p q u v u' v' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k l ->
      TaggedOptionPayloadDescentImageClassifier S T delta l m ->
        hsame k p ->
          hsame m q ->
            T u ->
              T v ->
                hsame p (BHist.e1 u) ->
                  hsame q (BHist.e1 v) ->
                    T u' ->
                      T v' ->
                        hsame p (BHist.e1 u') ->
                          hsame q (BHist.e1 v') ->
                            RelT u v /\ hsame u u' /\ hsame v v' /\
                              (hsame p BHist.Empty -> False) /\
                                (hsame q BHist.Empty -> False) := by
  intro imageKL imageLM sameKP sameMQ targetU targetV samePU sameQV targetU' targetV'
    samePU' sameQV'
  have relUV : RelT u v :=
    TaggedOptionPayloadDescentImageClassifier_reflective_transitive_transport_visible_target_payload_classification
      delta certS certT source_hsame target_hsame reflects imageKL imageLM sameKP sameMQ
      targetU targetV samePU sameQV
  have sameUU' : hsame u u' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm samePU) samePU')
  have sameVV' : hsame v v' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameQV) sameQV')
  have notPEmpty : hsame p BHist.Empty -> False := by
    intro samePEmpty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm samePU) samePEmpty)
  have notQEmpty : hsame q BHist.Empty -> False := by
    intro sameQEmpty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameQV) sameQEmpty)
  exact And.intro relUV
    (And.intro sameUU' (And.intro sameVV' (And.intro notPEmpty notQEmpty)))

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
    {S U : BHist → Prop} {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (certS : NameCert S RelS)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' x y : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' →
      hsame m u →
        hsame m' u' →
          U x →
            U y →
              hsame u (BHist.e1 x) →
                hsame u' (BHist.e1 y) →
                  RelU x y := by
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y
  have transported :
      TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) u u' :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      (TaggedOptionDescentComp delta epsilon) certS source_hsame image sameMU sameM'U'
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
      (TaggedOptionDescentComp delta epsilon) certS source_hsame transported targetX targetY
      sameUX sameU'Y
  cases readback with
  | intro a readback =>
      cases readback with
      | intro b data =>
          have relImage : RelU ((TaggedOptionDescentComp delta epsilon).map a)
              ((TaggedOptionDescentComp delta epsilon).map b) :=
            (TaggedOptionDescentComp delta epsilon).respects data.right.right.left
          have relLeft : RelU x ((TaggedOptionDescentComp delta epsilon).map a) :=
            target_hsame targetX data.right.right.right.left
              data.right.right.right.right.right.left
          have relRight : RelU ((TaggedOptionDescentComp delta epsilon).map b) y :=
            target_hsame data.right.right.right.right.left targetY
              (hsame_symm data.right.right.right.right.right.right)
          exact NameCert.equiv_trans certU (NameCert.equiv_trans certU relLeft relImage) relRight

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_payload_determinacy
    {S U : BHist → Prop} {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (certS : NameCert S RelS)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' x y x' y' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' →
      hsame m u →
        hsame m' u' →
          U x →
            U y →
              hsame u (BHist.e1 x) →
                hsame u' (BHist.e1 y) →
                  U x' →
                    U y' →
                      hsame u (BHist.e1 x') →
                        hsame u' (BHist.e1 y') →
                          RelU x y ∧ RelU x' y' ∧ hsame x x' ∧ hsame y y' ∧
                            (hsame u BHist.Empty → False) ∧
                              (hsame u' BHist.Empty → False) := by
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y targetX' targetY'
    sameUX' sameU'Y'
  have relXY : RelU x y :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
      delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U' targetX
      targetY sameUX sameU'Y
  have relX'Y' : RelU x' y' :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
      delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U' targetX'
      targetY' sameUX' sameU'Y'
  have sameXX' : hsame x x' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameUX) sameUX')
  have sameYY' : hsame y y' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameU'Y) sameU'Y')
  have notUEmpty : hsame u BHist.Empty → False := by
    intro sameUEmpty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameUX) sameUEmpty)
  have notU'Empty : hsame u' BHist.Empty → False := by
    intro sameU'Empty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameU'Y) sameU'Empty)
  exact And.intro relXY
    (And.intro relX'Y'
      (And.intro sameXX' (And.intro sameYY' (And.intro notUEmpty notU'Empty))))

end BEDC.Derived.OptionUp
