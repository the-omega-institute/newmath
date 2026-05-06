import BEDC.Derived.ComplexUp
import BEDC.Derived.ComplexSeriesUp
import BEDC.Derived.NatUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexSeriesUp
open BEDC.Derived.ComplexUp
open BEDC.Derived.NatUp

def GeomBound (a : Nat -> BHist) (r K : BHist) : Prop :=
  UnaryHistory r ∧ UnaryHistory K ∧ ∀ n : Nat, ComplexHistoryCarrier (a n)

def PowerSeriesCarrier (a : Nat -> BHist) (z0 : BHist) : Prop :=
  UnaryHistory z0 ∧ (∀ n : Nat, ComplexHistoryCarrier (a n)) ∧ ComplexHistoryCarrier z0

def PowerSeriesPartSum (a : Nat -> BHist) (z0 n S : BHist) : Prop :=
  PowerSeriesCarrier a z0 ∧ ComplexPartSum z0 (fun _ : BHist => a 0) n S

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

theorem PowerSeriesCarrier_append_unary_closed {a : Nat -> BHist} {z0 q : BHist} :
    PowerSeriesCarrier a z0 -> UnaryHistory q ->
      PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) := by
  intro carrier qUnary
  exact And.intro (unary_append_closed carrier.left qUnary)
    (And.intro
      (fun n : Nat => ComplexHistoryCarrier_append_unary_closed (carrier.right.left n) qUnary)
      (ComplexHistoryCarrier_append_unary_closed carrier.right.right qUnary))

theorem PowerSeriesCarrier_prepend_unary_closed {a : Nat -> BHist} {z0 q : BHist} :
    PowerSeriesCarrier a z0 -> UnaryHistory q ->
      PowerSeriesCarrier (fun n : Nat => append q (a n)) (append q z0) := by
  intro carrier qUnary
  exact And.intro (unary_append_closed qUnary carrier.left)
    (And.intro
      (fun n : Nat => ComplexHistoryCarrier_prepend_unary_closed qUnary (carrier.right.left n))
      (ComplexHistoryCarrier_prepend_unary_closed qUnary carrier.right.right))

def ConvRad (a : Nat -> BHist) (R : BHist) : Prop :=
  UnaryHistory R ∧ ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r ->
    Cont r (K r) R -> GeomBound a r (K r)

def ConvRadCauchyHadamardExactnessRow (a : Nat -> BHist) (R witness : BHist) : Prop :=
  ConvRad a R ∧ UnaryHistory R ∧ UnaryHistory witness ∧ Cont R witness R

def ConvRadClassifierSpec (R R' : BHist) : Prop :=
  UnaryHistory R ∧ UnaryHistory R' ∧ hsame R R'

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

theorem ConvRadClassifierSpec_radius_transport {a : Nat -> BHist} {R R' : BHist} :
    ConvRadClassifierSpec R R' -> ConvRad a R -> ConvRad a R' ∧ UnaryHistory R' := by
  intro classifier radius
  exact And.intro
    (ConvRad_radius_transport classifier.right.right radius classifier.right.left)
    classifier.right.left

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

theorem ConvRad_coefficient_ring_inclusion_monotone {a a' : Nat -> BHist} {rho : BHist} :
    UnaryHistory rho -> (forall n : Nat, ComplexHistoryClassifier (a n) (a' n)) ->
      ConvRad a rho -> ConvRad a' rho := by
  intro rhoUnary coeffClassified radius
  cases radius with
  | intro _radiusUnary witness =>
      cases witness with
      | intro K boundAt =>
          exact And.intro rhoUnary
            (Exists.intro K
              (fun {r : BHist} rUnary continuation =>
                let sourceBound := boundAt rUnary continuation
                And.intro sourceBound.left
                  (And.intro sourceBound.right.left
                    (fun n : Nat => (coeffClassified n).right.left))))

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

theorem GeomBound_visible_constant_endpoint_package {a : Nat -> BHist} {r R tail : BHist} :
    GeomBound a r (BHist.e1 tail) -> Cont r (BHist.e1 tail) R ->
      UnaryHistory tail ∧ (hsame R BHist.Empty -> False) := by
  intro bound continuation
  constructor
  · exact unary_e1_inversion bound.right.left
  · intro resultEmpty
    have emptyContinuation : Cont r (BHist.e1 tail) BHist.Empty :=
      cont_result_hsame_transport continuation resultEmpty
    have emptyParts := cont_empty_result_inversion emptyContinuation
    exact not_hsame_e1_empty emptyParts.right

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

theorem ConvRad_checked_rows_do_not_force_cauchy_hadamard {a : Nat -> BHist} {R : BHist} :
    ConvRad a R -> UnaryHistory R ->
      ∃ accept reject : BHist, (hsame accept reject -> False) ∧
        (ConvRad a R ∧ hsame R R) ∧ (ConvRad a R ∧ hsame R R) := by
  intro radius _radiusUnary
  exact Exists.intro BHist.Empty
    (Exists.intro (BHist.e1 BHist.Empty)
      (And.intro
        (fun sameAcceptReject => not_hsame_e1_empty (hsame_symm sameAcceptReject))
        (And.intro
          (And.intro radius (hsame_refl R))
          (And.intro radius (hsame_refl R)))))

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

theorem GeomBound_radius_shrink_closed {a : Nat -> BHist} {r' r K : BHist} :
    NatUnaryStrictPrefix r' r -> GeomBound a r K -> UnaryHistory r' ∧ GeomBound a r' K := by
  intro strict bound
  cases strict with
  | intro tail data =>
      have radiusUnary : UnaryHistory r' :=
        unary_cont_left_factor data.right.right bound.left
      exact And.intro radiusUnary
        (And.intro radiusUnary (And.intro bound.right.left bound.right.right))

def ConvRadPatternSpec (a : Nat -> BHist) (R r K : BHist) : Prop :=
  ConvRad a R ∧ GeomBound a r K

theorem ConvRadPatternSpec_radius_shrink_closed {a : Nat -> BHist} {R r' r K : BHist} :
    NatUnaryStrictPrefix r' r -> ConvRadPatternSpec a R r K ->
      UnaryHistory r' ∧ ConvRadPatternSpec a R r' K := by
  intro strict pattern
  have shrink := GeomBound_radius_shrink_closed strict pattern.right
  exact And.intro shrink.left (And.intro pattern.left shrink.right)

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

theorem GeomBound_prepend_unary_coeff_closed {a : Nat -> BHist} {r K q : BHist} :
    UnaryHistory q -> GeomBound a r K -> GeomBound (fun n : Nat => append q (a n)) r K := by
  intro qUnary bound
  exact And.intro bound.left
    (And.intro bound.right.left
      (fun n : Nat => ComplexHistoryCarrier_prepend_unary_closed qUnary (bound.right.right n)))

theorem ConvRad_append_unary_coeff_closed {a : Nat -> BHist} {R q : BHist} :
    ConvRad a R -> UnaryHistory q -> ConvRad (fun n : Nat => append (a n) q) R := by
  intro radius qUnary
  cases radius with
  | intro radiusUnary witness =>
      cases witness with
      | intro K boundAt =>
          exact And.intro radiusUnary
            (Exists.intro K
              (fun {r : BHist} rUnary continuation =>
                GeomBound_append_unary_coeff_closed (boundAt rUnary continuation) qUnary))

theorem ConvRad_prepend_unary_coeff_closed {a : Nat -> BHist} {R q : BHist} :
    ConvRad a R -> UnaryHistory q -> ConvRad (fun n : Nat => append q (a n)) R := by
  intro radius qUnary
  cases radius with
  | intro radiusUnary witness =>
      cases witness with
      | intro K boundAt =>
          exact And.intro radiusUnary
            (Exists.intro K
              (fun {r : BHist} rUnary continuation =>
                GeomBound_prepend_unary_coeff_closed qUnary (boundAt rUnary continuation)))

theorem ConvRad_successor_coefficients_closed {a : Nat -> BHist} {R : BHist} :
    ConvRad a R -> ConvRad (fun n : Nat => a (Nat.succ n)) R := by
  intro radius
  cases radius with
  | intro radiusUnary witness =>
      cases witness with
      | intro K boundAt =>
          exact And.intro radiusUnary
            (Exists.intro K
              (fun {r : BHist} rUnary continuation =>
                let sourceBound := boundAt rUnary continuation
                show GeomBound (fun n : Nat => a (Nat.succ n)) r (K r) from
                And.intro sourceBound.left
                  (And.intro sourceBound.right.left
                    (fun n : Nat => sourceBound.right.right (Nat.succ n)))))

theorem ConvRad_coefficient_tail_closed {a : Nat -> BHist} {R : BHist} :
    ConvRad a R -> UnaryHistory R ∧ ConvRad (fun n : Nat => a (Nat.succ n)) R := by
  intro radius
  exact And.intro radius.left (ConvRad_successor_coefficients_closed radius)

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

theorem ConvRad_powerSeriesCarrier_append_unary_witness
    {a : Nat -> BHist} {R z0 q : BHist} :
    ConvRad a R -> ComplexHistoryCarrier z0 -> UnaryHistory q ->
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
        PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) ∧
          GeomBound (fun n : Nat => append (a n) q) r (K r) := by
  intro radius centerCarrier qUnary
  cases ConvRad_powerSeriesCarrier_witness radius centerCarrier with
  | intro K witnessAt =>
      exact Exists.intro K (by
        intro r radiusUnary contRadius
        have source := witnessAt radiusUnary contRadius
        exact And.intro
          (PowerSeriesCarrier_append_unary_closed source.left qUnary)
          (GeomBound_append_unary_coeff_closed source.right qUnary))

theorem ConvRad_powerSeriesCarrier_prepend_unary_witness
    {a : Nat -> BHist} {R z0 q : BHist} :
    ConvRad a R -> ComplexHistoryCarrier z0 -> UnaryHistory q ->
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
        PowerSeriesCarrier (fun n : Nat => append q (a n)) (append q z0) ∧
          GeomBound (fun n : Nat => append q (a n)) r (K r) := by
  intro radius centerCarrier qUnary
  cases ConvRad_powerSeriesCarrier_witness radius centerCarrier with
  | intro K witnessAt =>
      exact Exists.intro K (by
        intro r radiusUnary contRadius
        have source := witnessAt radiusUnary contRadius
        exact And.intro
          (PowerSeriesCarrier_prepend_unary_closed source.left qUnary)
          (GeomBound_prepend_unary_coeff_closed qUnary source.right))

theorem GeomBound_radius_constant_continuation_closed {a : Nat -> BHist}
    {r K dr dK R K' : BHist} :
    GeomBound a r K -> UnaryHistory dr -> UnaryHistory dK -> Cont r dr R -> Cont K dK K' ->
      GeomBound a R K' := by
  intro bound radiusStep constantStep radiusContinuation constantContinuation
  exact And.intro (unary_cont_closed bound.left radiusStep radiusContinuation)
    (And.intro (unary_cont_closed bound.right.left constantStep constantContinuation)
      bound.right.right)

theorem GeomBound_radius_constant_hsame_transport_unary {a : Nat -> BHist}
    {r r' K K' : BHist} :
    hsame r r' -> hsame K K' -> GeomBound a r K ->
      UnaryHistory r' ∧ UnaryHistory K' ∧ GeomBound a r' K' := by
  intro sameRadius sameConstant bound
  have radiusUnary : UnaryHistory r' :=
    unary_transport bound.left sameRadius
  have constantUnary : UnaryHistory K' :=
    unary_transport bound.right.left sameConstant
  exact And.intro radiusUnary
    (And.intro constantUnary
      (And.intro radiusUnary
        (And.intro constantUnary bound.right.right)))

theorem GeomBound_continuation_visible_radius_endpoint_package {a : Nat -> BHist}
    {r K dr dK K' R tail : BHist} :
    GeomBound a r K -> UnaryHistory dr -> UnaryHistory dK ->
      Cont r dr (BHist.e1 tail) -> Cont K dK K' -> Cont (BHist.e1 tail) K' R ->
        UnaryHistory tail ∧ (hsame R BHist.Empty -> False) := by
  intro bound radiusStep constantStep radiusContinuation constantContinuation visibleContinuation
  have visibleBound : GeomBound a (BHist.e1 tail) K' :=
    GeomBound_radius_constant_continuation_closed bound radiusStep constantStep
      radiusContinuation constantContinuation
  exact GeomBound_visible_radius_endpoint_package visibleBound visibleContinuation

theorem ConvRad_visible_radius_witness_endpoint_package {a : Nat -> BHist} {R tail : BHist} :
    ConvRad a R -> UnaryHistory (BHist.e1 tail) ->
      ∃ K : BHist -> BHist, Cont (BHist.e1 tail) (K (BHist.e1 tail)) R ->
        UnaryHistory tail ∧ (hsame R BHist.Empty -> False) := by
  intro radius visibleRadius
  cases radius with
  | intro _radiusCarrier witness =>
      cases witness with
      | intro K boundAt =>
          exact Exists.intro K (by
            intro continuation
            have bound : GeomBound a (BHist.e1 tail) (K (BHist.e1 tail)) :=
              boundAt visibleRadius continuation
            exact GeomBound_visible_radius_endpoint_package bound continuation)

theorem ConvRad_classifier_visible_radius_witness_endpoint_package
    {a b : Nat -> BHist} {R R' tail : BHist} :
    hsame R R' -> UnaryHistory R' -> (forall n : Nat, ComplexHistoryClassifier (a n) (b n)) ->
      ConvRad a R -> UnaryHistory (BHist.e1 tail) ->
        ∃ K : BHist -> BHist, Cont (BHist.e1 tail) (K (BHist.e1 tail)) R' ->
          UnaryHistory tail ∧ (hsame R' BHist.Empty -> False) := by
  intro sameRadius targetUnary coeffClassified radius visibleRadius
  have transported :
      UnaryHistory R' ∧ ConvRad b R' :=
    ConvRad_radius_coefficient_classifier_transport sameRadius targetUnary coeffClassified radius
  exact ConvRad_visible_radius_witness_endpoint_package transported.right visibleRadius

theorem PowerSeriesComplexPartSum_exists_unique {zero n : BHist} {term : BHist -> BHist} :
    ComplexHistoryCarrier zero ->
      (forall {m : BHist}, UnaryHistory m -> ComplexHistoryCarrier (term m)) ->
        UnaryHistory n ->
          exists S : BHist, ComplexPartSum zero term n S ∧ ComplexHistoryCarrier S ∧
            forall T : BHist, ComplexPartSum zero term n T -> hsame S T := by
  intro zeroCarrier termCarrier unaryN
  refine (unary_history_induction
    (P := fun index =>
      exists S : BHist, ComplexPartSum zero term index S ∧ ComplexHistoryCarrier S ∧
        forall T : BHist, ComplexPartSum zero term index T -> hsame S T)
    ?base ?step n unaryN)
  · exact Exists.intro zero
      (And.intro ComplexPartSum.zero
        (And.intro zeroCarrier
          (fun T other => ComplexPartSum_deterministic ComplexPartSum.zero other)))
  · intro m unaryM previous
    cases previous with
    | intro S data =>
        have current :
            ComplexPartSum zero term (BHist.e1 m) (append S (term m)) :=
          ComplexPartSum.step data.left (cont_intro rfl)
        have termUnary : UnaryHistory (term m) :=
          ComplexHistoryCarrier_unary (termCarrier unaryM)
        have currentCarrier : ComplexHistoryCarrier (append S (term m)) :=
          ComplexHistoryCarrier_append_unary_closed data.right.left termUnary
        exact Exists.intro (append S (term m))
          (And.intro current
            (And.intro currentCarrier
              (fun T other => ComplexPartSum_deterministic current other)))

theorem PowerSeriesCarrier_constant_coeff_partSum_exists_unique {a : Nat -> BHist} {z0 n : BHist} :
    PowerSeriesCarrier a z0 -> UnaryHistory n ->
      ∃ S : BHist, PowerSeriesPartSum a z0 n S ∧ ComplexHistoryCarrier S ∧
        ∀ T : BHist, PowerSeriesPartSum a z0 n T -> hsame S T := by
  intro carrier unaryN
  have constantCoeff :
      ∀ {m : BHist}, UnaryHistory m -> ComplexHistoryCarrier ((fun _ : BHist => a 0) m) :=
    fun {_m : BHist} _unaryM => carrier.right.left 0
  cases PowerSeriesComplexPartSum_exists_unique carrier.right.right constantCoeff unaryN with
  | intro S data =>
      exact Exists.intro S
        (And.intro
          (And.intro carrier data.left)
          (And.intro data.right.left
            (fun T part =>
              data.right.right T part.right)))

def ConvRadSourceSpec (a : Nat -> BHist) (z0 R : BHist) : Prop :=
  PowerSeriesCarrier a z0 ∧ ConvRad a R

theorem ConvRadSourceSpec_powerSeries_append_prepend_closed {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadSourceSpec a z0 R -> UnaryHistory q ->
      PowerSeriesCarrier (fun n : Nat => append (a n) q) (append z0 q) ∧
        PowerSeriesCarrier (fun n : Nat => append q (a n)) (append q z0) := by
  intro source qUnary
  exact And.intro
    (PowerSeriesCarrier_append_unary_closed source.left qUnary)
    (PowerSeriesCarrier_prepend_unary_closed source.left qUnary)

theorem ConvRadSourceSpec_powerSeries_geomBound_readback {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadSourceSpec a z0 R ->
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
        PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) ∧ UnaryHistory R := by
  intro source
  cases source with
  | intro carrier radius =>
      cases ConvRad_powerSeriesCarrier_witness radius carrier.right.right with
      | intro K readback =>
          exact Exists.intro K (by
            intro r radiusUnary continuation
            have row := readback radiusUnary continuation
            exact And.intro row.left (And.intro row.right radius.left))

theorem ConvRad_stability_certificate_fields {a b : Nat -> BHist} {R q : BHist} :
    (forall {h : BHist}, hsame h h) ∧
    (forall {h k : BHist}, hsame h k -> hsame k h) ∧
    (forall {h k r : BHist}, hsame h k -> hsame k r -> hsame h r) ∧
    (forall {R' : BHist}, hsame R R' -> UnaryHistory R' -> ConvRad a R -> ConvRad a R') ∧
    ((forall n : Nat, ComplexHistoryClassifier (a n) (b n)) -> ConvRad a R -> ConvRad b R) ∧
    (ConvRad a R -> UnaryHistory q -> ConvRad (fun n : Nat => append (a n) q) R) := by
  exact And.intro
    (fun {h : BHist} => hsame_refl h)
    (And.intro
      (fun {h k : BHist} same => hsame_symm same)
      (And.intro
        (fun {h k r : BHist} sameHK sameKR => hsame_trans sameHK sameKR)
        (And.intro
          (fun {R' : BHist} sameRadius targetUnary radius =>
            ConvRad_radius_transport sameRadius radius targetUnary)
          (And.intro
            (fun coeffClassified radius =>
              (ConvRad_radius_coefficient_classifier_transport (hsame_refl R) radius.left
                coeffClassified radius).right)
            (fun radius qUnary => ConvRad_append_unary_coeff_closed radius qUnary)))))

def ConvRadCheckedRowReduct (a : Nat -> BHist) (z0 R : BHist) : Prop :=
  ConvRadSourceSpec a z0 R ∧
    ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
      PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) ∧ UnaryHistory R

theorem ConvRadSourceSpec_checkedRowReduct_readback {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadSourceSpec a z0 R -> ConvRadCheckedRowReduct a z0 R := by
  intro source
  exact And.intro source (ConvRadSourceSpec_powerSeries_geomBound_readback source)

def ConvRadRadiusClassifierSpec (a b : Nat -> BHist) (R R' : BHist) : Prop :=
  ConvRad a R ∧ hsame R R' ∧ UnaryHistory R' ∧
    forall n : Nat, ComplexHistoryClassifier (a n) (b n)

theorem ConvRadRadiusClassifierSpec_powerSeries_witness
    {a b : Nat -> BHist} {R R' z0 : BHist} :
    ConvRadRadiusClassifierSpec a b R R' -> ComplexHistoryCarrier z0 ->
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R' ->
        PowerSeriesCarrier b z0 ∧ GeomBound b r (K r) ∧ hsame R R' := by
  intro classifier centerCarrier
  have transported :
      UnaryHistory R' ∧ ConvRad b R' :=
    ConvRad_radius_coefficient_classifier_transport classifier.right.left
      classifier.right.right.left classifier.right.right.right classifier.left
  cases ConvRad_powerSeriesCarrier_witness transported.right centerCarrier with
  | intro K readback =>
      exact Exists.intro K (by
        intro r radiusUnary continuation
        have row := readback radiusUnary continuation
        exact And.intro row.left (And.intro row.right classifier.right.left))

def ConvRadLedgerPolicy (a : Nat -> BHist) (z0 R : BHist) : Prop :=
  ConvRadCheckedRowReduct a z0 R ∧ forall {q : BHist}, UnaryHistory q ->
    ConvRad (fun n : Nat => append (a n) q) R ∧ ConvRad (fun n : Nat => append q (a n)) R

theorem ConvRadCheckedRowReduct_append_prepend_ledger
    {a : Nat -> BHist} {z0 R q : BHist} :
    ConvRadCheckedRowReduct a z0 R -> UnaryHistory q ->
      ConvRadLedgerPolicy a z0 R ∧ ConvRad (fun n : Nat => append (a n) q) R ∧
        ConvRad (fun n : Nat => append q (a n)) R := by
  intro checked qUnary
  have radius : ConvRad a R := checked.left.right
  have appendRadius : ConvRad (fun n : Nat => append (a n) q) R :=
    ConvRad_append_unary_coeff_closed radius qUnary
  have prependRadius : ConvRad (fun n : Nat => append q (a n)) R :=
    ConvRad_prepend_unary_coeff_closed radius qUnary
  exact And.intro
    (And.intro checked
      (fun {_q : BHist} qUnary' =>
        And.intro
          (ConvRad_append_unary_coeff_closed radius qUnary')
          (ConvRad_prepend_unary_coeff_closed radius qUnary')))
    (And.intro appendRadius prependRadius)

theorem conv_rad_name_certificate :
    NameCert (fun R : BHist => exists a : Nat -> BHist, ConvRad a R) hsame := by
  let coefficient : BHist := append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
  let constantFamily : Nat -> BHist := fun _n : Nat => coefficient
  have denominatorCarrier : RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Iff.mpr RatUp.RatHistoryCarrier_iff_positive_denominator
      (Iff.mpr RatUp.PositiveUnaryDenominator_e1_iff_unary unary_empty)
  have coefficientCarrier : ComplexHistoryCarrier coefficient :=
    Exists.intro (BHist.e1 BHist.Empty)
      (Exists.intro (BHist.e1 BHist.Empty)
        (And.intro denominatorCarrier
          (And.intro denominatorCarrier (cont_intro rfl))))
  have radius : ConvRad constantFamily (BHist.e1 BHist.Empty) := by
    exact And.intro (unary_e1_closed unary_empty)
      (Exists.intro (fun _r : BHist => BHist.Empty)
        (fun {r : BHist} rUnary _continuation =>
          And.intro rUnary
            (And.intro unary_empty
              (fun _n : Nat => coefficientCarrier))))
  exact {
    carrier_inhabited :=
      Exists.intro (BHist.e1 BHist.Empty)
        (Exists.intro constantFamily radius)
    equiv_refl := by
      intro R _source
      exact hsame_refl R
    equiv_symm := by
      intro R R' same
      exact hsame_symm same
    equiv_trans := by
      intro R R' R'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro R R' same source
      cases source with
      | intro a radiusR =>
          exact Exists.intro a
            (ConvRad_radius_transport same radiusR (unary_transport radiusR.left same))
  }

end BEDC.Derived.ConvergenceRadiusUp
