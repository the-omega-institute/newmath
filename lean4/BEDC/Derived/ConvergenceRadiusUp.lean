import BEDC.Derived.ComplexUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def GeomBound (a : Nat -> BHist) (r K : BHist) : Prop :=
  UnaryHistory r ∧ UnaryHistory K ∧ ∀ n : Nat, ComplexHistoryCarrier (a n)

def PowerSeriesCarrier (a : Nat -> BHist) (z0 : BHist) : Prop :=
  UnaryHistory z0 /\ forall n : Nat, ComplexHistoryCarrier (a n)

theorem PowerSeriesCarrier_origin_coefficient_transport {a b : Nat -> BHist} {z0 z0' : BHist} :
    hsame z0 z0' -> (forall n : Nat, ComplexHistoryClassifier (a n) (b n)) ->
      PowerSeriesCarrier a z0 -> UnaryHistory z0' /\ PowerSeriesCarrier b z0' := by
  intro sameOrigin coeffClassified carrier
  have targetOrigin : UnaryHistory z0' := unary_transport carrier.left sameOrigin
  exact And.intro targetOrigin
    (And.intro targetOrigin (fun n => (coeffClassified n).right.left))

def ConvRad (a : Nat -> BHist) (R : BHist) : Prop :=
  UnaryHistory R ∧ ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r ->
    Cont r (K r) R -> GeomBound a r (K r)

theorem ConvRad_radius_transport {a : Nat -> BHist} {R R' : BHist} :
    hsame R R' -> ConvRad a R -> UnaryHistory R' -> ConvRad a R' := by
  intro sameRadius radius targetUnary
  cases sameRadius
  cases radius with
  | intro _ witness =>
      exact And.intro targetUnary witness

end BEDC.Derived.ConvergenceRadiusUp
