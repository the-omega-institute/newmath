import BEDC.Derived.OptionUp.PayloadDescentImageClassifierReadback

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_public_factorization_representative_independent
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (certU : NameCert U RelU)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible U RelU)
    {m m' u u' x y x' y' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          U x ->
            U y ->
              hsame u (BHist.e1 x) ->
                hsame u' (BHist.e1 y) ->
                  U x' ->
                    U y' ->
                      hsame u (BHist.e1 x') ->
                        hsame u' (BHist.e1 y') ->
                          RelU x y ∧ RelU x' y' ∧ RelU x y' ∧ RelU x' y := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  intro image sameMU sameM'U' targetX targetY sameUX sameU'Y targetX' targetY'
    sameUX' sameU'Y'
  have _certTCarrier : exists h : BHist, T h := certT.carrier_inhabited
  have clique :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_visible_payload_clique
      delta epsilon certS certU source_hsame target_hsame image sameMU sameM'U'
      targetX targetY sameUX sameU'Y targetX' targetY' sameUX' sameU'Y'
  have relXY : RelU x y := clique.left
  have relXY' : RelU x y' := clique.right.left
  have relX'Y : RelU x' y := clique.right.right.left
  have relX'Y' : RelU x' y' := clique.right.right.right.left
  exact And.intro relXY (And.intro relX'Y' (And.intro relXY' relX'Y))

end BEDC.Derived.OptionUp
