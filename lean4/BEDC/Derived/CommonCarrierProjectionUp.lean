import BEDC.Algebra.Rel.Basic
import BEDC.Derived.NonCollapseInvariantUp

namespace BEDC.Derived.CommonCarrierProjectionUp

open BEDC.Algebra.Rel
open BEDC.Derived.LocatedReal
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.FKernel.Hist

universe u v w

abbrev ValueRat : Type :=
  BEDC.Derived.LocatedReal.Rat

structure ProjectionLedger where
  observed : List BHist
  observed_nodup : observed.Nodup
  hidden : List BHist
  hidden_nodup : hidden.Nodup
  scopedRows : List BHist
  scopedRows_nodup : scopedRows.Nodup
  refused : List BHist
  refused_nodup : refused.Nodup
  transport : List BHist
  transport_nodup : transport.Nodup
  provenance : List BHist
  provenance_nodup : provenance.Nodup

def ProjectionLedger.rowCount (ledger : ProjectionLedger) (row : BHist) : Nat :=
  ledger.observed.count row +
    ledger.hidden.count row +
      ledger.scopedRows.count row +
        ledger.refused.count row +
          ledger.transport.count row +
            ledger.provenance.count row

structure RealityInterface where
  Carrier : Type u
  classifier : RelEquiv Carrier
  admissible : Carrier → Prop
  observations : Carrier → List BHist
  ledger : Carrier → ProjectionLedger

structure CommonCarrier (Index : Type v) where
  source : RealityInterface.{u}
  target : Index → RealityInterface.{w}
  project : (i : Index) → source.Carrier → (target i).Carrier
  project_respects :
    ∀ (i : Index) {x y : source.Carrier},
      source.classifier.rel x y →
        (target i).classifier.rel (project i x) (project i y)
  projectionLedger : (i : Index) → source.Carrier → ProjectionLedger

def ProjectionProperty {Index : Type v} (carrier : CommonCarrier.{u, v, w} Index)
    (i : Index) (predicate : (carrier.target i).Carrier → Prop)
    (x : carrier.source.Carrier) : Prop :=
  predicate (carrier.project i x)

theorem projection_preserves_classified_identity
    {Index : Type v} (carrier : CommonCarrier.{u, v, w} Index)
    (i : Index) {x y : carrier.source.Carrier}
    (same : carrier.source.classifier.rel x y) :
    (carrier.target i).classifier.rel
      (carrier.project i x) (carrier.project i y) :=
  carrier.project_respects i same

structure LosslessRetraction
    {Shadow : Type u} {Source : Type v}
    (shadowEq : RelEquiv Shadow) (sourceEq : RelEquiv Source)
    (project : Source → Shadow) where
  reconstruct : Shadow → Source
  reconstruct_respects :
    ∀ {x y : Shadow}, shadowEq.rel x y →
      sourceEq.rel (reconstruct x) (reconstruct y)
  recovers :
    ∀ x : Source, sourceEq.rel (reconstruct (project x)) x

structure NontrivialProjectionFiber
    {Shadow : Type u} {Source : Type v}
    (shadowEq : RelEquiv Shadow) (sourceEq : RelEquiv Source)
    (project : Source → Shadow) where
  left : Source
  right : Source
  same_shadow : shadowEq.rel (project left) (project right)
  separated : sourceEq.rel left right → False

theorem nontrivial_fiber_no_lossless_retraction
    {Shadow : Type u} {Source : Type v}
    {shadowEq : RelEquiv Shadow} {sourceEq : RelEquiv Source}
    {project : Source → Shadow}
    (fiber : NontrivialProjectionFiber shadowEq sourceEq project) :
    LosslessRetraction shadowEq sourceEq project → False := by
  intro retraction
  have leftBack :
      sourceEq.rel fiber.left (retraction.reconstruct (project fiber.left)) :=
    sourceEq.symm (retraction.recovers fiber.left)
  have reconstructedSame :
      sourceEq.rel (retraction.reconstruct (project fiber.left))
        (retraction.reconstruct (project fiber.right)) :=
    retraction.reconstruct_respects fiber.same_shadow
  have rightBack :
      sourceEq.rel (retraction.reconstruct (project fiber.right)) fiber.right :=
    retraction.recovers fiber.right
  exact fiber.separated
    (sourceEq.trans leftBack (sourceEq.trans reconstructedSame rightBack))

def locatedShadow {K : RatMetricKit} (point : LReal K) (precision : Nat) :
    ValueRat :=
  point.seq (point.modulus precision)

structure LocatedRealProjectionLedger (K : RatMetricKit) where
  point : LReal K
  precision : Nat
  shadow : ValueRat
  shadow_eq : shadow = locatedShadow point precision
  ledger : ProjectionLedger

def locatedRealProjectionLedger {K : RatMetricKit}
    (point : LReal K) (precision : Nat) (ledger : ProjectionLedger) :
    LocatedRealProjectionLedger K where
  point := point
  precision := precision
  shadow := locatedShadow point precision
  shadow_eq := rfl
  ledger := ledger

def LocatedRealValueRetraction (K : RatMetricKit) (point : LReal K) : Prop :=
  ∃ q : ValueRat, LRealEq K point (ratToLReal K q)

theorem located_real_noncollapse_forbids_value_retraction
    {K : RatMetricKit} (sep : SeparatingRatMetricKit K)
    (witness : NonCollapseWitness K) :
    LocatedRealValueRetraction K witness.point → False := by
  intro collapse
  exact (NonCollapseWitness_no_rat_retraction sep witness) collapse

theorem located_real_noncollapse_projection_is_lossy
    {K : RatMetricKit} (sep : SeparatingRatMetricKit K)
    (witness : NonCollapseWitness K) :
    (∃ q : ValueRat, LRealEq K witness.point (ratToLReal K q)) → False :=
  located_real_noncollapse_forbids_value_retraction sep witness

end BEDC.Derived.CommonCarrierProjectionUp
