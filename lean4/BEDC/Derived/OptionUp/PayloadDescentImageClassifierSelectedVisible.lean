import BEDC.Derived.OptionUp.PayloadDescentImageClassifierReadback

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_selected_visible_public_pair_canonicality
    {S U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (certS : NameCert S RelS)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU) {m m' u u' x y : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          U x ->
            U y ->
              hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) ->
                  RelU x y /\
                    (forall x' : BHist, U x' -> hsame u (BHist.e1 x') ->
                      hsame x x' /\ RelU x' y) /\
                    (forall y' : BHist, U y' -> hsame u' (BHist.e1 y') ->
                      hsame y y' /\ RelU x y') /\
                    (hsame u BHist.Empty -> False) /\ (hsame u' BHist.Empty -> False) := by
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y
  have relXY : RelU x y :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
      delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U'
      targetX targetY sameUX sameU'Y
  have leftCanonical :
      forall x' : BHist, U x' -> hsame u (BHist.e1 x') ->
        hsame x x' /\ RelU x' y := by
    intro x' targetX' sameUX'
    have sameXX' : hsame x x' :=
      hsame_e1_iff.mp (hsame_trans (hsame_symm sameUX) sameUX')
    have relX'Y : RelU x' y :=
      TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
        delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U'
        targetX' targetY sameUX' sameU'Y
    exact And.intro sameXX' relX'Y
  have rightCanonical :
      forall y' : BHist, U y' -> hsame u' (BHist.e1 y') ->
        hsame y y' /\ RelU x y' := by
    intro y' targetY' sameU'Y'
    have sameYY' : hsame y y' :=
      hsame_e1_iff.mp (hsame_trans (hsame_symm sameU'Y) sameU'Y')
    have relXY' : RelU x y' :=
      TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_target_payload_classification
        delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U'
        targetX targetY' sameUX sameU'Y'
    exact And.intro sameYY' relXY'
  have notUEmpty : hsame u BHist.Empty -> False := by
    intro sameUEmpty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameUX) sameUEmpty)
  have notU'Empty : hsame u' BHist.Empty -> False := by
    intro sameU'Empty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameU'Y) sameU'Empty)
  exact And.intro relXY
    (And.intro leftCanonical
      (And.intro rightCanonical (And.intro notUEmpty notU'Empty)))

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_selected_visible_public_factorization
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (middle_hsame : TaggedOptionSourceHsameCompatible T RelT)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU) {m m' u u' x y : BHist} :
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
                      T p /\ T q /\ U (epsilon.map p) /\ U (epsilon.map q) /\
                      hsame k (BHist.e1 p) /\ hsame k' (BHist.e1 q) /\
                      hsame x (epsilon.map p) /\ hsame y (epsilon.map q) /\
                      S a /\ S b /\ RelS a b /\ T (delta.map a) /\
                      T (delta.map b) /\ hsame p (delta.map a) /\
                      hsame q (delta.map b) /\ RelT p q /\ RelU x y /\
                      (hsame u BHist.Empty -> False) /\
                      (hsame u' BHist.Empty -> False) /\
                      (forall x' : BHist, U x' -> hsame u (BHist.e1 x') ->
                        hsame x x' /\ RelU x' y) /\
                      (forall y' : BHist, U y' -> hsame u' (BHist.e1 y') ->
                        hsame y y' /\ RelU x y') := by
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y
  have canonical :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_selected_visible_public_pair_canonicality
      delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U'
      targetX targetY sameUX sameU'Y
  have relXY : RelU x y := canonical.left
  have leftCanonical :
      forall x' : BHist, U x' -> hsame u (BHist.e1 x') ->
        hsame x x' /\ RelU x' y := canonical.right.left
  have rightCanonical :
      forall y' : BHist, U y' -> hsame u' (BHist.e1 y') ->
        hsame y y' /\ RelU x y' := canonical.right.right.left
  have notUEmpty : hsame u BHist.Empty -> False := canonical.right.right.right.left
  have notU'Empty : hsame u' BHist.Empty -> False := canonical.right.right.right.right
  have oneSided :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_one_sided_visible_public_factorization
      delta epsilon rhoD certS certT certU source_hsame middle_hsame target_hsame
      image sameMU sameM'U'
  have selected := oneSided.left x targetX sameUX
  cases selected with
  | intro y0 selected =>
      cases selected with
      | intro k selected =>
          cases selected with
          | intro k' selected =>
              cases selected with
              | intro p selected =>
                  cases selected with
                  | intro q selected =>
                      cases selected with
                      | intro a selected =>
                          cases selected with
                          | intro b data =>
                              cases data with
                              | intro targetY0 data =>
                                  cases data with
                                  | intro sameU'Y0 data =>
                                      cases data with
                                      | intro _relXY0 data =>
                                          cases data with
                                          | intro imageDelta data =>
                                              cases data with
                                              | intro mapLeft data =>
                                                  cases data with
                                                  | intro mapRight data =>
                                                      cases data with
                                                      | intro targetP data =>
                                                          cases data with
                                                          | intro targetQ data =>
                                                              cases data with
                                                              | intro imageP data =>
                                                                  cases data with
                                                                  | intro imageQ data =>
                                                                      cases data with
                                                                      | intro sameKP data =>
                                                                          cases data with
                                                                          | intro sameK'Q data =>
                                                                              cases data with
                                                                              | intro sameXP data =>
                                                                                  cases data with
                                                                                  | intro sameY0Q data =>
                                                                                      cases data with
                                                                                      | intro sourceA data =>
                                                                                          cases data with
                                                                                          | intro sourceB data =>
                                                                                              cases data with
                                                                                              | intro relAB data =>
                                                                                                  cases data with
                                                                                                  | intro targetDeltaA data =>
                                                                                                      cases data with
                                                                                                      | intro targetDeltaB data =>
                                                                                                          cases data with
                                                                                                          | intro samePDeltaA data =>
                                                                                                              cases data with
                                                                                                              | intro sameQDeltaB data =>
                                                                                                                  cases data with
                                                                                                                  | intro relPQ _rest =>
                                                                                                                      have sameYY0 : hsame y y0 :=
                                                                                                                        (rightCanonical y0
                                                                                                                          targetY0
                                                                                                                          sameU'Y0).left
                                                                                                                      have sameYQ :
                                                                                                                          hsame y
                                                                                                                            (epsilon.map q) :=
                                                                                                                        hsame_trans
                                                                                                                          sameYY0
                                                                                                                          sameY0Q
                                                                                                                      exact
                                                                                                                        ⟨k, k', p, q, a, b,
                                                                                                                          imageDelta,
                                                                                                                          mapLeft,
                                                                                                                          mapRight,
                                                                                                                          targetP,
                                                                                                                          targetQ,
                                                                                                                          imageP,
                                                                                                                          imageQ,
                                                                                                                          sameKP,
                                                                                                                          sameK'Q,
                                                                                                                          sameXP,
                                                                                                                          sameYQ,
                                                                                                                          sourceA,
                                                                                                                          sourceB,
                                                                                                                          relAB,
                                                                                                                          targetDeltaA,
                                                                                                                          targetDeltaB,
                                                                                                                          samePDeltaA,
                                                                                                                          sameQDeltaB,
                                                                                                                          relPQ,
                                                                                                                          relXY,
                                                                                                                          notUEmpty,
                                                                                                                          notU'Empty,
                                                                                                                          leftCanonical,
                                                                                                                          rightCanonical⟩

end BEDC.Derived.OptionUp
