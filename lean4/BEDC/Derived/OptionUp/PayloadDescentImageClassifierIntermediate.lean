import BEDC.Derived.OptionUp.BranchExactness
import BEDC.Derived.OptionUp.CompositeAbsentPublicFactorization
import BEDC.Derived.OptionUp.PayloadDescentImageClassifierReadback

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_present_intermediate_payload_determinacy
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (middle_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' x y : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          U x ->
            U y ->
              hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) ->
                  exists k k' p q a b : BHist,
                    TaggedOptionPayloadDescentImageClassifier S T delta k k' /\
                      TaggedOptionMapRel T U epsilon k u /\
                        TaggedOptionMapRel T U epsilon k' u' /\
                          T p /\ T q /\ hsame k (BHist.e1 p) /\
                            hsame k' (BHist.e1 q) /\ S a /\ S b /\ RelS a b /\
                              hsame p (delta.map a) /\ hsame q (delta.map b) /\
                                (forall r : BHist, hsame k (BHist.e1 r) -> hsame p r) /\
                                  (forall s : BHist,
                                    hsame k' (BHist.e1 s) -> hsame q s) := by
  intro image sameMU sameM'U' targetX _targetY sameUX _sameU'Y
  have factorized :=
    (TaggedOptionPayloadDescentImageClassifier_composite_normalized_one_sided_visible_public_factorization
      delta epsilon rhoD certS certT certU source_hsame middle_hsame target_hsame image
      sameMU sameM'U').left x targetX sameUX
  cases factorized with
  | intro selectedY rest =>
      cases rest with
      | intro k rest =>
          cases rest with
          | intro k' rest =>
              cases rest with
              | intro p rest =>
                  cases rest with
                  | intro q rest =>
                      cases rest with
                      | intro a rest =>
                          cases rest with
                          | intro b data =>
                              have imageDelta :
                                  TaggedOptionPayloadDescentImageClassifier S T delta k k' :=
                                data.right.right.right.left
                              have mapLeft : TaggedOptionMapRel T U epsilon k u :=
                                data.right.right.right.right.left
                              have mapRight : TaggedOptionMapRel T U epsilon k' u' :=
                                data.right.right.right.right.right.left
                              have targetP : T p :=
                                data.right.right.right.right.right.right.left
                              have targetQ : T q :=
                                data.right.right.right.right.right.right.right.left
                              have sameKP : hsame k (BHist.e1 p) :=
                                data.right.right.right.right.right.right.right.right.right.right.left
                              have sameK'Q : hsame k' (BHist.e1 q) :=
                                data.right.right.right.right.right.right.right.right.right.right.right.left
                              have sourceA : S a :=
                                data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                              have sourceB : S b :=
                                data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                              have relAB : RelS a b :=
                                data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                              have samePDelta : hsame p (delta.map a) :=
                                data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                              have sameQDelta : hsame q (delta.map b) :=
                                data.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                              have uniqueLeft :
                                  forall r : BHist, hsame k (BHist.e1 r) -> hsame p r := by
                                intro r sameKR
                                exact TaggedOptionHistory_present_payload_determinism sameKP sameKR
                              have uniqueRight :
                                  forall s : BHist, hsame k' (BHist.e1 s) -> hsame q s := by
                                intro s sameK'S
                                exact TaggedOptionHistory_present_payload_determinism sameK'Q sameK'S
                              exact
                                ⟨k, k', p, q, a, b, imageDelta, mapLeft, mapRight,
                                  targetP, targetQ, sameKP, sameK'Q, sourceA, sourceB,
                                  relAB, samePDelta, sameQDelta, uniqueLeft, uniqueRight⟩

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_present_intermediate_classifier_determinacy
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (middle_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' x y : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          U x ->
            U y ->
              hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) ->
                  exists k k' p q a b : BHist,
                    TaggedOptionPayloadDescentImageClassifier S T delta k k' /\
                      TaggedOptionMapRel T U epsilon k u /\
                        TaggedOptionMapRel T U epsilon k' u' /\
                          T p /\ T q /\ hsame k (BHist.e1 p) /\
                            hsame k' (BHist.e1 q) /\ S a /\ S b /\ RelS a b /\
                              hsame p (delta.map a) /\ hsame q (delta.map b) /\
                                TaggedOptionHistoryClassifier T RelT k k' /\
                                  (forall r s : BHist, T r -> T s ->
                                    hsame k (BHist.e1 r) ->
                                      hsame k' (BHist.e1 s) -> RelT r s) := by
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y
  have payload :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_present_intermediate_payload_determinacy
      delta epsilon rhoD certS certT certU source_hsame middle_hsame target_hsame
      image sameMU sameM'U' targetX targetY sameUX sameU'Y
  cases payload with
  | intro k payload =>
      cases payload with
      | intro k' payload =>
          cases payload with
          | intro p payload =>
              cases payload with
              | intro q payload =>
                  cases payload with
                  | intro a payload =>
                      cases payload with
                      | intro b data =>
                          have imageDelta :
                              TaggedOptionPayloadDescentImageClassifier S T delta k k' :=
                            data.left
                          have mapLeft : TaggedOptionMapRel T U epsilon k u :=
                            data.right.left
                          have mapRight : TaggedOptionMapRel T U epsilon k' u' :=
                            data.right.right.left
                          have targetP : T p := data.right.right.right.left
                          have targetQ : T q := data.right.right.right.right.left
                          have sameKP : hsame k (BHist.e1 p) :=
                            data.right.right.right.right.right.left
                          have sameK'Q : hsame k' (BHist.e1 q) :=
                            data.right.right.right.right.right.right.left
                          have sourceA : S a :=
                            data.right.right.right.right.right.right.right.left
                          have sourceB : S b :=
                            data.right.right.right.right.right.right.right.right.left
                          have relAB : RelS a b :=
                            data.right.right.right.right.right.right.right.right.right.left
                          have samePDelta : hsame p (delta.map a) :=
                            data.right.right.right.right.right.right.right.right.right.right.left
                          have sameQDelta : hsame q (delta.map b) :=
                            data.right.right.right.right.right.right.right.right.right.right.right.left
                          have targetDeltaA : T (delta.map a) := rhoD a sourceA
                          have targetDeltaB : T (delta.map b) := rhoD b sourceB
                          have relPDelta : RelT p (delta.map a) :=
                            middle_hsame targetP targetDeltaA samePDelta
                          have relDeltaAB : RelT (delta.map a) (delta.map b) :=
                            delta.respects relAB
                          have relDeltaQ : RelT (delta.map b) q :=
                            middle_hsame targetDeltaB targetQ (hsame_symm sameQDelta)
                          have relPQ : RelT p q :=
                            NameCert.equiv_trans certT
                              (NameCert.equiv_trans certT relPDelta relDeltaAB) relDeltaQ
                          have classifier : TaggedOptionHistoryClassifier T RelT k k' :=
                            Or.inr ⟨p, q, targetP, targetQ, sameKP, sameK'Q, relPQ⟩
                          have uniquePair :
                              (forall r : BHist, hsame k (BHist.e1 r) -> hsame p r) /\
                                (forall s : BHist, hsame k' (BHist.e1 s) -> hsame q s) :=
                            data.right.right.right.right.right.right.right.right.right.right.right.right
                          have competing :
                              forall r s : BHist, T r -> T s -> hsame k (BHist.e1 r) ->
                                hsame k' (BHist.e1 s) -> RelT r s := by
                            intro r s targetR targetS sameKR sameK'S
                            have samePR :
                                hsame p r :=
                              uniquePair.left r sameKR
                            have sameQS :
                                hsame q s :=
                              uniquePair.right s sameK'S
                            have relPR : RelT p r := middle_hsame targetP targetR samePR
                            have relQS : RelT q s := middle_hsame targetQ targetS sameQS
                            exact NameCert.equiv_trans certT
                              (NameCert.equiv_trans certT (NameCert.equiv_symm certT relPR)
                                relPQ)
                              relQS
                          exact
                            ⟨k, k', p, q, a, b, imageDelta, mapLeft, mapRight, targetP,
                              targetQ, sameKP, sameK'Q, sourceA, sourceB, relAB,
                              samePDelta, sameQDelta, classifier, competing⟩

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_intermediate_classifier_coverage
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (rhoE : forall b : BHist, T b -> U (epsilon.map b))
    (epsilon_hsame : forall x y : BHist, T x -> T y -> hsame x y ->
      hsame (epsilon.map x) (epsilon.map y))
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (middle_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          exists k k' : BHist,
            TaggedOptionPayloadDescentImageClassifier S T delta k k' ∧
              TaggedOptionMapRel T U epsilon k u ∧
                TaggedOptionMapRel T U epsilon k' u' ∧
                  TaggedOptionHistoryClassifier T RelT k k' := by
  intro image sameMU sameM'U'
  have transported :
      TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon)
        u u' :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      (TaggedOptionDescentComp delta epsilon) certS source_hsame image sameMU sameM'U'
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness
      (TaggedOptionDescentComp delta epsilon) certS source_hsame).mp transported
  cases branch with
  | inl absent =>
      have factorized :=
        TaggedOptionPayloadDescentImageClassifier_composite_normalized_absent_public_factorization
          delta epsilon rhoD rhoE epsilon_hsame certS source_hsame image sameMU sameM'U'
          absent.left absent.right
      cases factorized with
      | intro k factorized =>
          cases factorized with
          | intro k' data =>
              have classifier : TaggedOptionHistoryClassifier T RelT k k' :=
                Or.inl (And.intro data.right.right.right.left data.right.right.right.right.left)
              exact
                ⟨k, k', data.left, data.right.left, data.right.right.left, classifier⟩
  | inr present =>
      cases present with
      | intro a present =>
          cases present with
          | intro b data =>
              have targetX : U (epsilon.map (delta.map a)) :=
                data.right.right.right.left
              have targetY : U (epsilon.map (delta.map b)) :=
                data.right.right.right.right.left
              have sameUX : hsame u (BHist.e1 (epsilon.map (delta.map a))) :=
                data.right.right.right.right.right.left
              have sameU'Y : hsame u' (BHist.e1 (epsilon.map (delta.map b))) :=
                data.right.right.right.right.right.right
              have presentWitness :=
                TaggedOptionPayloadDescentImageClassifier_composite_normalized_present_intermediate_classifier_determinacy
                  delta epsilon rhoD certS certT certU source_hsame middle_hsame target_hsame
                  image sameMU sameM'U' targetX targetY sameUX sameU'Y
              cases presentWitness with
              | intro k presentWitness =>
                  cases presentWitness with
                  | intro k' presentWitness =>
                      cases presentWitness with
                      | intro _p presentWitness =>
                          cases presentWitness with
                          | intro _q presentWitness =>
                              cases presentWitness with
                              | intro _a presentWitness =>
                                  cases presentWitness with
                                  | intro _b witnessData =>
                                      exact
                                        ⟨k, k', witnessData.left, witnessData.right.left,
                                          witnessData.right.right.left,
                                          witnessData.right.right.right.right.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.OptionUp
