import BEDC.Derived.ComplexUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def GeomBound (a : Nat -> BHist) (r K : BHist) : Prop :=
  UnaryHistory r ∧ UnaryHistory K ∧ ∀ n : Nat, ComplexHistoryCarrier (a n)

def PowerSeriesCarrier (a : Nat -> BHist) (z0 : BHist) : Prop :=
  UnaryHistory z0 ∧ (∀ n : Nat, ComplexHistoryCarrier (a n)) ∧ ComplexHistoryCarrier z0

theorem PowerSeriesCarrier_origin_coefficient_transport {a b : Nat -> BHist} {z0 z0' : BHist} :
    hsame z0 z0' -> (∀ n : Nat, ComplexHistoryClassifier (a n) (b n)) ->
      PowerSeriesCarrier a z0 -> UnaryHistory z0' ∧ PowerSeriesCarrier b z0' := by
  intro sameOrigin coeffClassified carrier
  have targetOrigin : UnaryHistory z0' := unary_transport carrier.left sameOrigin
  have targetOriginComplex : ComplexHistoryCarrier z0' :=
    BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport sameOrigin carrier.right.right
  exact And.intro targetOrigin
    (And.intro targetOrigin
      (And.intro (fun n => (coeffClassified n).right.left) targetOriginComplex))

def ConvRad (a : Nat -> BHist) (R : BHist) : Prop :=
  UnaryHistory R ∧ ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r ->
    Cont r (K r) R -> GeomBound a r (K r)

theorem GeomBound_powerSeriesCarrier {a : Nat -> BHist} {r K z0 : BHist} :
    GeomBound a r K -> ComplexHistoryCarrier z0 ->
      PowerSeriesCarrier a z0 ∧ UnaryHistory r ∧ UnaryHistory K := by
  intro bound centerCarrier
  cases bound with
  | intro radiusUnary rest =>
      cases rest with
      | intro constantUnary coeffCarrier =>
          exact And.intro
            (And.intro (ComplexHistoryCarrier_unary centerCarrier)
              (And.intro coeffCarrier centerCarrier))
            (And.intro radiusUnary constantUnary)

theorem ConvRad_radius_transport {a : Nat -> BHist} {R R' : BHist} :
    hsame R R' -> ConvRad a R -> UnaryHistory R' -> ConvRad a R' := by
  intro sameRadius radius targetUnary
  cases sameRadius
  cases radius with
  | intro _ witness =>
      exact And.intro targetUnary witness

theorem ConvRad_radius_coefficient_classifier_transport {a b : Nat -> BHist} {R R' : BHist} :
    hsame R R' -> UnaryHistory R' -> (forall n : Nat, ComplexHistoryClassifier (a n) (b n)) ->
      ConvRad a R -> UnaryHistory R' ∧ ConvRad b R' := by
  intro sameRadius targetUnary coeffClassified radius
  have movedRadius : ConvRad a R' :=
    ConvRad_radius_transport sameRadius radius targetUnary
  cases movedRadius with
  | intro _ witness =>
      cases witness with
      | intro K bound =>
          exact And.intro targetUnary
            (And.intro targetUnary
              (Exists.intro K
                (fun {r : BHist} rUnary continuation =>
                  let sourceBound := bound rUnary continuation
                  And.intro sourceBound.left
                    (And.intro sourceBound.right.left
                      (fun n => (coeffClassified n).right.left)))))

theorem GeomBound_visible_radius_endpoint_package {a : Nat -> BHist} {K R tail : BHist} :
    GeomBound a (BHist.e1 tail) K -> Cont (BHist.e1 tail) K R ->
      UnaryHistory tail ∧ (hsame R BHist.Empty -> False) := by
  intro bound continuation
  constructor
  · exact unary_e1_inversion bound.left
  · intro resultEmpty
    have emptyContinuation : Cont (BHist.e1 tail) K BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    have emptyParts := cont_empty_result_inversion emptyContinuation
    exact not_hsame_e1_empty emptyParts.left

theorem ConvRad_semanticNameCert {a : Nat -> BHist} {R : BHist} (radius : ConvRad a R) :
    SemanticNameCert (ConvRad a) (ConvRad a) (ConvRad a) hsame := by
  constructor
  · constructor
    · exact Exists.intro R radius
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact ConvRad_radius_transport same carrier (unary_transport carrier.left same)
  · intro _h source
    exact source
  · intro _h source
    exact source

theorem GeomBound_radius_semanticNameCert {a : Nat -> BHist} {r K : BHist}
    (bound : GeomBound a r K) :
    SemanticNameCert (fun radius : BHist => GeomBound a radius K)
      (fun radius : BHist => GeomBound a radius K)
      (fun radius : BHist => GeomBound a radius K) hsame := by
  constructor
  · constructor
    · exact Exists.intro r bound
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k q sameHK sameKQ
      exact hsame_trans sameHK sameKQ
    · intro h k same carrier
      exact And.intro (unary_transport carrier.left same) carrier.right
  · intro _h source
    exact source
  · intro _h source
    exact source

theorem GeomBound_semanticNameCert {a : Nat -> BHist} {r K : BHist}
    (bound : GeomBound a r K) :
    SemanticNameCert (fun x : BHist => GeomBound a x K)
      (fun x : BHist => GeomBound a x K) (fun x : BHist => GeomBound a x K) hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro r bound
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        exact And.intro (unary_transport carrier.left same)
          (And.intro carrier.right.left carrier.right.right)
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

theorem GeomBound_coeff_classifier_append_unary_closed {a b : Nat -> BHist} {r K q : BHist} :
    (forall n : Nat, ComplexHistoryClassifier (a n) (b n)) -> GeomBound a r K ->
      UnaryHistory q -> GeomBound (fun n : Nat => append (b n) q) r K := by
  intro classified bound qUnary
  exact And.intro bound.left
    (And.intro bound.right.left
      (fun n : Nat => ComplexHistoryCarrier_append_unary_closed (classified n).right.left qUnary))

theorem GeomBound_append_unary_coeff_closed {a : Nat -> BHist} {r K q : BHist} :
    GeomBound a r K -> UnaryHistory q -> GeomBound (fun n : Nat => append (a n) q) r K := by
  intro bound qUnary
  exact And.intro bound.left
    (And.intro bound.right.left
      (fun n : Nat => ComplexHistoryCarrier_append_unary_closed (bound.right.right n) qUnary))

theorem ConvRad_powerSeriesCarrier_witness {a : Nat -> BHist} {R z0 : BHist} :
    ConvRad a R -> ComplexHistoryCarrier z0 ->
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
        PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) := by
  intro radius centerCarrier
  cases radius with
  | intro _ witness =>
      cases witness with
      | intro K boundAt =>
          exact Exists.intro K (by
            intro r radiusUnary contRadius
            have bound : GeomBound a r (K r) := boundAt radiusUnary contRadius
            exact And.intro (GeomBound_powerSeriesCarrier bound centerCarrier).left bound)

theorem GeomBound_radius_constant_continuation_closed {a : Nat -> BHist}
    {r K dr dK R K' : BHist} :
    GeomBound a r K -> UnaryHistory dr -> UnaryHistory dK -> Cont r dr R -> Cont K dK K' ->
      GeomBound a R K' := by
  intro bound radiusStep constantStep radiusContinuation constantContinuation
  exact And.intro (unary_cont_closed bound.left radiusStep radiusContinuation)
    (And.intro (unary_cont_closed bound.right.left constantStep constantContinuation)
      bound.right.right)

end BEDC.Derived.ConvergenceRadiusUp
