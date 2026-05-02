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

end BEDC.Derived.OptionUp
