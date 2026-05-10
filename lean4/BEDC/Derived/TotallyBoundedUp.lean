import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RatUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TotallyBoundedUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp

def TotallyBoundedProbeBundleNet (X : BHist -> Prop) (eps : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  RatHistoryCarrier eps ∧
    (forall {p : BHist}, InBundle p bundle -> X p) ∧
      (forall {x : BHist}, X x ->
        exists p : BHist, InBundle p bundle ∧
          exists d : BHist, MetricDistanceWitness x p d ∧ RatHistoryClassifier d eps)

def TotallyBoundedProbeBundleNetSubcarrierRestriction (X Y : BHist -> Prop) (eps : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  RatHistoryCarrier eps ∧
    (forall {p : BHist}, InBundle p bundle -> X p) ∧
      (forall {y : BHist}, Y y ->
        exists p : BHist, InBundle p bundle ∧
          exists d : BHist, MetricDistanceWitness y p d ∧ RatHistoryClassifier d eps)

theorem TotallyBoundedProbeBundleNet_coverage_hsame_transport {X : BHist -> Prop}
    {eps eps' : BHist} {bundle : ProbeBundle BHist} :
    hsame eps eps' -> TotallyBoundedProbeBundleNet X eps bundle ->
      TotallyBoundedProbeBundleNet X eps' bundle := by
  intro sameEps net
  cases net with
  | intro epsCarrier rest =>
      constructor
      · exact RatHistoryCarrier_hsame_transport sameEps epsCarrier
      · constructor
        · exact rest.left
        · intro x sourceX
          cases rest.right sourceX with
          | intro p pData =>
              cases pData.right with
              | intro d distanceData =>
                  exact ⟨p, pData.left, d, distanceData.left,
                    RatHistoryClassifier_hsame_transport (hsame_refl d) sameEps
                      distanceData.right⟩

theorem TotallyBoundedProbeBundleNet_tolerance_weakening {X : BHist -> Prop}
    {eps eps' : BHist} {bundle : ProbeBundle BHist} :
    RatHistoryClassifier eps eps' -> TotallyBoundedProbeBundleNet X eps bundle ->
      TotallyBoundedProbeBundleNet X eps' bundle := by
  intro tolerance net
  cases tolerance with
  | intro epsCarrier toleranceRest =>
      cases toleranceRest with
      | intro epsCarrier' sameEps =>
          cases net with
          | intro _netEpsCarrier netRest =>
              constructor
              · exact epsCarrier'
              · constructor
                · exact netRest.left
                · intro x sourceX
                  cases netRest.right sourceX with
                  | intro p pData =>
                      cases pData.right with
                      | intro d distanceData =>
                          have dToEps' : RatHistoryClassifier d eps' :=
                            RatHistoryClassifier_trans distanceData.right
                              (And.intro epsCarrier (And.intro epsCarrier' sameEps))
                          exact ⟨p, pData.left, d, distanceData.left, dToEps'⟩

theorem TotallyBoundedProbeBundleNet_name_certificate {X : BHist -> Prop} {eps : BHist}
    {bundle : ProbeBundle BHist} :
    TotallyBoundedProbeBundleNet X eps bundle ->
      SemanticNameCert
        (fun eps' : BHist => TotallyBoundedProbeBundleNet X eps' bundle)
        (fun eps' : BHist => TotallyBoundedProbeBundleNet X eps' bundle)
        (fun eps' : BHist => TotallyBoundedProbeBundleNet X eps' bundle) hsame := by
  intro net
  exact {
    core := {
      carrier_inhabited := Exists.intro eps net
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro _h _k same carrier
        exact TotallyBoundedProbeBundleNet_coverage_hsame_transport same carrier
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

theorem TotallyBoundedProbeBundleNet_finite_union {X Y : BHist -> Prop} {eps : BHist}
    {left right : ProbeBundle BHist} :
    TotallyBoundedProbeBundleNet X eps left ->
      TotallyBoundedProbeBundleNet Y eps right ->
        TotallyBoundedProbeBundleNet (fun z : BHist => X z ∨ Y z) eps
          (bundleAppend left right) := by
  intro leftNet rightNet
  cases leftNet with
  | intro epsCarrier leftRest =>
      cases rightNet with
      | intro _epsCarrierRight rightRest =>
          constructor
          · exact epsCarrier
          · constructor
            · intro p inAppended
              cases (inBundle_bundleAppend_iff (p := p) (left := left) (right := right)).mp
                  inAppended with
              | inl inLeft =>
                  exact Or.inl (leftRest.left inLeft)
              | inr inRight =>
                  exact Or.inr (rightRest.left inRight)
            · intro x unionSource
              cases unionSource with
              | inl sourceX =>
                  cases leftRest.right sourceX with
                  | intro p pData =>
                      cases pData.right with
                      | intro d distanceData =>
                          exact ⟨p,
                            (inBundle_bundleAppend_iff (p := p) (left := left)
                              (right := right)).mpr (Or.inl pData.left),
                            d, distanceData.left, distanceData.right⟩
              | inr sourceY =>
                  cases rightRest.right sourceY with
                  | intro p pData =>
                      cases pData.right with
                      | intro d distanceData =>
                          exact ⟨p,
                            (inBundle_bundleAppend_iff (p := p) (left := left)
                              (right := right)).mpr (Or.inr pData.left),
                            d, distanceData.left, distanceData.right⟩

theorem TotallyBoundedProbeBundleNet_append_membership_separation
    {X Y : BHist -> Prop} {eps : BHist} {left right : ProbeBundle BHist} {p : BHist} :
    TotallyBoundedProbeBundleNet X eps left -> TotallyBoundedProbeBundleNet Y eps right ->
      InBundle p (bundleAppend left right) ->
        (InBundle p left ∧ X p) ∨ (InBundle p right ∧ Y p) := by
  intro leftNet rightNet inAppended
  cases leftNet with
  | intro _epsCarrier leftRest =>
      cases rightNet with
      | intro _epsCarrierRight rightRest =>
          cases (inBundle_bundleAppend_iff (p := p) (left := left) (right := right)).mp
              inAppended with
          | inl inLeft =>
              exact Or.inl (And.intro inLeft (leftRest.left inLeft))
          | inr inRight =>
              exact Or.inr (And.intro inRight (rightRest.left inRight))

theorem TotallyBoundedProbeBundleNet_subcarrier_restriction {X Y : BHist -> Prop}
    {eps : BHist} {bundle : ProbeBundle BHist}
    (inclusion : forall {y : BHist}, Y y -> X y)
    (centerY : forall {p : BHist}, InBundle p bundle -> Y p) :
    TotallyBoundedProbeBundleNet X eps bundle -> TotallyBoundedProbeBundleNet Y eps bundle := by
  intro net
  cases net with
  | intro epsCarrier rest =>
      constructor
      · exact epsCarrier
      · constructor
        · intro p inBundle
          exact centerY inBundle
        · intro y sourceY
          cases rest.right (inclusion sourceY) with
          | intro p pData =>
              cases pData.right with
              | intro d distanceData =>
                  exact ⟨p, pData.left, d, distanceData.left, distanceData.right⟩

theorem TotallyBoundedProbeBundleNetSubcarrierRestriction_net_restricts {X Y : BHist -> Prop}
    {eps : BHist} {bundle : ProbeBundle BHist}
    (inclusion : forall {y : BHist}, Y y -> X y) :
    TotallyBoundedProbeBundleNet X eps bundle ->
      TotallyBoundedProbeBundleNetSubcarrierRestriction X Y eps bundle := by
  intro net
  cases net with
  | intro epsCarrier rest =>
      constructor
      · exact epsCarrier
      · constructor
        · exact rest.left
        · intro y sourceY
          exact rest.right (inclusion sourceY)

theorem SingletonMetricTotallyBounded_laws :
    hsame BHist.Empty BHist.Empty ∧
      InBundle BHist.Empty (ProbeBundle.Bcons BHist.Empty ProbeBundle.Bnil) ∧
        (forall {x : BHist}, hsame x BHist.Empty ->
          MetricDistanceWitness x BHist.Empty BHist.Empty) ∧
          (forall {x y : BHist}, hsame x BHist.Empty -> hsame y BHist.Empty ->
            hsame x y) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact inBundle_cons_self BHist.Empty ProbeBundle.Bnil
    · constructor
      · intro x sameX
        exact (MetricDistanceWitness_empty_distance_iff (x := x) (y := BHist.Empty)).mpr
          (And.intro sameX (hsame_refl BHist.Empty))
      · intro x y sameX sameY
        exact hsame_trans sameX (hsame_symm sameY)

end BEDC.Derived.TotallyBoundedUp
