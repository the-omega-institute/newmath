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
