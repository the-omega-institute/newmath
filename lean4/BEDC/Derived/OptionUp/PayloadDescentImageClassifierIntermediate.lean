import BEDC.Derived.OptionUp.BranchExactness
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

end BEDC.Derived.OptionUp
