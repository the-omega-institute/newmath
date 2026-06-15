import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistanceToCompactUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistanceToCompactUp : Type where
  | mk (metricPoint compactNet locatedComparison finiteWitness regularReadback realSeal
      transport replay provenance localName : BHist) :
      DistanceToCompactUp
  deriving DecidableEq

def distanceToCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: distanceToCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: distanceToCompactEncodeBHist h

def distanceToCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (distanceToCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (distanceToCompactDecodeBHist tail)

private theorem distanceToCompact_decode_encode_bhist :
    ∀ h : BHist, distanceToCompactDecodeBHist (distanceToCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem distanceToCompact_mk_congr
    {metricPoint metricPoint' compactNet compactNet' locatedComparison locatedComparison'
      finiteWitness finiteWitness' regularReadback regularReadback' realSeal realSeal'
      transport transport' replay replay' provenance provenance' localName localName' : BHist}
    (hMetricPoint : metricPoint' = metricPoint)
    (hCompactNet : compactNet' = compactNet)
    (hLocatedComparison : locatedComparison' = locatedComparison)
    (hFiniteWitness : finiteWitness' = finiteWitness)
    (hRegularReadback : regularReadback' = regularReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    DistanceToCompactUp.mk metricPoint' compactNet' locatedComparison' finiteWitness'
        regularReadback' realSeal' transport' replay' provenance' localName' =
      DistanceToCompactUp.mk metricPoint compactNet locatedComparison finiteWitness
        regularReadback realSeal transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetricPoint
  cases hCompactNet
  cases hLocatedComparison
  cases hFiniteWitness
  cases hRegularReadback
  cases hRealSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def distanceToCompactFields : DistanceToCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DistanceToCompactUp.mk metricPoint compactNet locatedComparison finiteWitness
      regularReadback realSeal transport replay provenance localName =>
      [metricPoint, compactNet, locatedComparison, finiteWitness, regularReadback,
        realSeal, transport, replay, provenance, localName]

def distanceToCompactToEventFlow : DistanceToCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (distanceToCompactFields x).map distanceToCompactEncodeBHist

def distanceToCompactFromEventFlow : EventFlow → Option DistanceToCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | metricPoint :: compactNet :: locatedComparison :: finiteWitness :: regularReadback ::
      realSeal :: transport :: replay :: provenance :: localName :: [] =>
      some
        (DistanceToCompactUp.mk
          (distanceToCompactDecodeBHist metricPoint)
          (distanceToCompactDecodeBHist compactNet)
          (distanceToCompactDecodeBHist locatedComparison)
          (distanceToCompactDecodeBHist finiteWitness)
          (distanceToCompactDecodeBHist regularReadback)
          (distanceToCompactDecodeBHist realSeal)
          (distanceToCompactDecodeBHist transport)
          (distanceToCompactDecodeBHist replay)
          (distanceToCompactDecodeBHist provenance)
          (distanceToCompactDecodeBHist localName))
  | _ => none

private theorem distanceToCompact_round_trip :
    ∀ x : DistanceToCompactUp,
      distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricPoint compactNet locatedComparison finiteWitness regularReadback realSeal
      transport replay provenance localName =>
      exact
        congrArg some
          (distanceToCompact_mk_congr
            (distanceToCompact_decode_encode_bhist metricPoint)
            (distanceToCompact_decode_encode_bhist compactNet)
            (distanceToCompact_decode_encode_bhist locatedComparison)
            (distanceToCompact_decode_encode_bhist finiteWitness)
            (distanceToCompact_decode_encode_bhist regularReadback)
            (distanceToCompact_decode_encode_bhist realSeal)
            (distanceToCompact_decode_encode_bhist transport)
            (distanceToCompact_decode_encode_bhist replay)
            (distanceToCompact_decode_encode_bhist provenance)
            (distanceToCompact_decode_encode_bhist localName))

private theorem distanceToCompactToEventFlow_injective {x y : DistanceToCompactUp} :
    distanceToCompactToEventFlow x = distanceToCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) =
        distanceToCompactFromEventFlow (distanceToCompactToEventFlow y) :=
    congrArg distanceToCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (distanceToCompact_round_trip x).symm
      (Eq.trans hread (distanceToCompact_round_trip y)))

private theorem distanceToCompact_field_faithful :
    ∀ x y : DistanceToCompactUp,
      distanceToCompactFields x = distanceToCompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricPoint compactNet locatedComparison finiteWitness regularReadback realSeal
      transport replay provenance localName =>
      cases y with
      | mk metricPoint' compactNet' locatedComparison' finiteWitness' regularReadback'
          realSeal' transport' replay' provenance' localName' =>
          cases hfields
          rfl

instance distanceToCompactBHistCarrier : BHistCarrier DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := distanceToCompactToEventFlow
  fromEventFlow := distanceToCompactFromEventFlow

instance distanceToCompactChapterTasteGate : ChapterTasteGate DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x
    exact distanceToCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (distanceToCompactToEventFlow_injective heq)

instance distanceToCompactFieldFaithful : FieldFaithful DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := distanceToCompactFields
  field_faithful := distanceToCompact_field_faithful

instance distanceToCompactNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DistanceToCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DistanceToCompactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DistanceToCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  distanceToCompactChapterTasteGate

def DistanceToCompactCarrier [AskSetup] [PackageSetup]
    (metricPoint compactNet locatedComparison finiteWitness regularReadback realSeal
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory metricPoint ∧ UnaryHistory compactNet ∧ UnaryHistory locatedComparison ∧
    UnaryHistory finiteWitness ∧ UnaryHistory regularReadback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg

theorem DistanceToCompactCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metricPoint compactNet locatedComparison finiteWitness regularReadback realSeal transport
      replay provenance localName request locatedRead finiteRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DistanceToCompactCarrier metricPoint compactNet locatedComparison finiteWitness
        regularReadback realSeal transport replay provenance localName bundle pkg →
      Cont metricPoint compactNet request →
        Cont request locatedComparison locatedRead →
          Cont locatedRead finiteWitness finiteRead →
            Cont finiteRead regularReadback regularRead →
              Cont regularRead realSeal realRead →
                PkgSig bundle realRead pkg →
                  UnaryHistory request ∧ UnaryHistory locatedRead ∧ UnaryHistory finiteRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier metricCompactRequest requestLocatedComparison locatedFiniteWitness
    finiteRegularReadback regularRealSeal _realPkg
  obtain ⟨metricPointUnary, compactNetUnary, locatedComparisonUnary, finiteWitnessUnary,
    regularReadbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed metricPointUnary compactNetUnary metricCompactRequest
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed requestUnary locatedComparisonUnary requestLocatedComparison
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed locatedReadUnary finiteWitnessUnary locatedFiniteWitness
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed finiteReadUnary regularReadbackUnary finiteRegularReadback
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularReadUnary realSealUnary regularRealSeal
  exact
    ⟨requestUnary, locatedReadUnary, finiteReadUnary, regularReadUnary, realReadUnary,
      provenancePkg⟩

end BEDC.Derived.DistanceToCompactUp
