import BEDC.Derived.OptionUp.CompositeNormalizedZeroEndpoint

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_public_endpoint_shape_certificate
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (middle_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU) {m m' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          (((hsame u BHist.Empty /\ hsame u' BHist.Empty /\
              (forall x y : BHist, U x -> U y -> hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) -> False) /\
              exists k k' : BHist,
                TaggedOptionPayloadDescentImageClassifier S T delta k k' /\
                  TaggedOptionMapRel T U epsilon k u /\
                    TaggedOptionMapRel T U epsilon k' u' /\
                      hsame k BHist.Empty /\ hsame k' BHist.Empty) \/
            (exists x y k k' p q a b : BHist,
              U x /\ U y /\ hsame u (BHist.e1 x) /\ hsame u' (BHist.e1 y) /\
                RelU x y /\ TaggedOptionPayloadDescentImageClassifier S T delta k k' /\
                  TaggedOptionMapRel T U epsilon k u /\
                    TaggedOptionMapRel T U epsilon k' u' /\
                      T p /\ T q /\ S a /\ S b /\ RelS a b /\ RelT p q)) /\
            (forall t : BHist, (hsame u (BHist.e0 t) -> False) /\
              (hsame u' (BHist.e0 t) -> False))) := by
  intro image sameMU sameM'U'
  have transported :
      TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) u u' :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      (TaggedOptionDescentComp delta epsilon) certS source_hsame image sameMU sameM'U'
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness
      (TaggedOptionDescentComp delta epsilon) certS source_hsame).mp transported
  have zeroExclusion :
      forall t : BHist, (hsame u (BHist.e0 t) -> False) /\
        (hsame u' (BHist.e0 t) -> False) :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_zero_endpoint_exclusion
      delta epsilon certS source_hsame image sameMU sameM'U'
  constructor
  · cases branch with
    | inl absent =>
        have visibleAbsurd :
            forall x y : BHist, U x -> U y -> hsame u (BHist.e1 x) ->
              hsame u' (BHist.e1 y) -> False := by
          intro x _y _targetX _targetY sameUX _sameU'Y
          exact not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameUX)
        have imageEmpty :
            TaggedOptionPayloadDescentImageClassifier S T delta BHist.Empty BHist.Empty := by
          apply (TaggedOptionPayloadDescentImageClassifier_branch_exactness
            delta certS source_hsame).mpr
          exact Or.inl (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
        have mapLeft : TaggedOptionMapRel T U epsilon BHist.Empty u :=
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.left)
        have mapRight : TaggedOptionMapRel T U epsilon BHist.Empty u' :=
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.right)
        exact Or.inl
          (And.intro absent.left
            (And.intro absent.right
              (And.intro visibleAbsurd
                (Exists.intro BHist.Empty
                  (Exists.intro BHist.Empty
                    (And.intro imageEmpty
                      (And.intro mapLeft
                        (And.intro mapRight
                          (And.intro (hsame_refl BHist.Empty)
                            (hsame_refl BHist.Empty))))))))))
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro relAB rest =>
                            cases rest with
                            | intro targetA rest =>
                                cases rest with
                                | intro targetB rest =>
                                    cases rest with
                                    | intro sameU sameU' =>
                                        have targetDeltaA : T (delta.map a) :=
                                          rhoD a sourceA
                                        have targetDeltaB : T (delta.map b) :=
                                          rhoD b sourceB
                                        have relDeltaBase : RelT (delta.map a) (delta.map b) :=
                                          delta.respects relAB
                                        have relDeltaRight :
                                            RelT (delta.map b) (delta.map b) :=
                                          middle_hsame targetDeltaB targetDeltaB
                                            (hsame_refl (delta.map b))
                                        have relDelta : RelT (delta.map a) (delta.map b) :=
                                          NameCert.equiv_trans certT relDeltaBase relDeltaRight
                                        have relTargetBase :
                                            RelU (epsilon.map (delta.map a))
                                              (epsilon.map (delta.map b)) :=
                                          epsilon.respects relDelta
                                        have relTargetRight :
                                            RelU (epsilon.map (delta.map b))
                                              (epsilon.map (delta.map b)) :=
                                          target_hsame targetB targetB
                                            (hsame_refl (epsilon.map (delta.map b)))
                                        have relTarget :
                                            RelU (epsilon.map (delta.map a))
                                              (epsilon.map (delta.map b)) :=
                                          NameCert.equiv_trans certU relTargetBase relTargetRight
                                        have imageDelta :
                                            TaggedOptionPayloadDescentImageClassifier S T delta
                                              (BHist.e1 (delta.map a))
                                              (BHist.e1 (delta.map b)) := by
                                          apply
                                            (TaggedOptionPayloadDescentImageClassifier_branch_exactness
                                              delta certS source_hsame).mpr
                                          exact Or.inr
                                            (Exists.intro a
                                              (Exists.intro b
                                                (And.intro sourceA
                                                  (And.intro sourceB
                                                    (And.intro relAB
                                                      (And.intro targetDeltaA
                                                        (And.intro targetDeltaB
                                                          (And.intro
                                                            (hsame_refl
                                                              (BHist.e1 (delta.map a)))
                                                            (hsame_refl
                                                              (BHist.e1 (delta.map b)))))))))))
                                        have mapLeft :
                                            TaggedOptionMapRel T U epsilon
                                              (BHist.e1 (delta.map a)) u :=
                                          Or.inr
                                            (Exists.intro (delta.map a)
                                              (And.intro targetDeltaA
                                                (And.intro targetA
                                                  (And.intro
                                                    (hsame_refl
                                                      (BHist.e1 (delta.map a)))
                                                    sameU))))
                                        have mapRight :
                                            TaggedOptionMapRel T U epsilon
                                              (BHist.e1 (delta.map b)) u' :=
                                          Or.inr
                                            (Exists.intro (delta.map b)
                                              (And.intro targetDeltaB
                                                (And.intro targetB
                                                  (And.intro
                                                    (hsame_refl
                                                      (BHist.e1 (delta.map b)))
                                                    sameU'))))
                                        exact Or.inr
                                          ⟨epsilon.map (delta.map a), epsilon.map (delta.map b),
                                            BHist.e1 (delta.map a), BHist.e1 (delta.map b),
                                            delta.map a, delta.map b, a, b, targetA, targetB,
                                            sameU, sameU', relTarget, imageDelta, mapLeft,
                                            mapRight, targetDeltaA, targetDeltaB, sourceA,
                                            sourceB, relAB, relDelta⟩
  · exact zeroExclusion

end BEDC.Derived.OptionUp
