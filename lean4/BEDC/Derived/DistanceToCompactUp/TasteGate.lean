import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistanceToCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistanceToCompactUp : Type where
  | mk (X K L F R E H C P N : BHist) : DistanceToCompactUp
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

private theorem DistanceToCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, distanceToCompactDecodeBHist (distanceToCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def distanceToCompactFields : DistanceToCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DistanceToCompactUp.mk X K L F R E H C P N => [X, K, L, F, R, E, H, C, P, N]

def distanceToCompactToEventFlow : DistanceToCompactUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (distanceToCompactFields x).map distanceToCompactEncodeBHist

private def distanceToCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => distanceToCompactEventAtDefault index rest

def distanceToCompactFromEventFlow (ef : EventFlow) : Option DistanceToCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DistanceToCompactUp.mk
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 0 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 1 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 2 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 3 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 4 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 5 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 6 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 7 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 8 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 9 ef)))

private theorem DistanceToCompactTasteGate_single_carrier_alignment_round_trip
    (x : DistanceToCompactUp) :
    distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X K L F R E H C P N =>
      change
        some
          (DistanceToCompactUp.mk
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist X))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist K))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist L))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist F))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist R))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist E))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist H))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist C))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist P))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist N))) =
          some (DistanceToCompactUp.mk X K L F R E H C P N)
      rw [DistanceToCompactTasteGate_single_carrier_alignment_decode X,
        DistanceToCompactTasteGate_single_carrier_alignment_decode K,
        DistanceToCompactTasteGate_single_carrier_alignment_decode L,
        DistanceToCompactTasteGate_single_carrier_alignment_decode F,
        DistanceToCompactTasteGate_single_carrier_alignment_decode R,
        DistanceToCompactTasteGate_single_carrier_alignment_decode E,
        DistanceToCompactTasteGate_single_carrier_alignment_decode H,
        DistanceToCompactTasteGate_single_carrier_alignment_decode C,
        DistanceToCompactTasteGate_single_carrier_alignment_decode P,
        DistanceToCompactTasteGate_single_carrier_alignment_decode N]

private theorem DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DistanceToCompactUp} :
    distanceToCompactToEventFlow x = distanceToCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) =
        distanceToCompactFromEventFlow (distanceToCompactToEventFlow y) :=
    congrArg distanceToCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DistanceToCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DistanceToCompactTasteGate_single_carrier_alignment_round_trip y)))

private theorem DistanceToCompactTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DistanceToCompactUp, distanceToCompactFields x = distanceToCompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X K L F R E H C P N =>
      cases y with
      | mk X' K' L' F' R' E' H' C' P' N' =>
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
    exact DistanceToCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance distanceToCompactFieldFaithful : FieldFaithful DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := distanceToCompactFields
  field_faithful := DistanceToCompactTasteGate_single_carrier_alignment_field_faithful

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

def distanceToCompactTasteGate : ChapterTasteGate DistanceToCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  distanceToCompactChapterTasteGate

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

theorem DistanceToCompactTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DistanceToCompactUp) ∧
      Nonempty (FieldFaithful DistanceToCompactUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DistanceToCompactUp) ∧
      distanceToCompactEncodeBHist BHist.Empty = [] ∧
        distanceToCompactEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
          distanceToCompactEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
            (∀ h : BHist,
              distanceToCompactDecodeBHist (distanceToCompactEncodeBHist h) = h) ∧
              (∀ x : DistanceToCompactUp,
                distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x) ∧
                Function.Injective distanceToCompactToEventFlow := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨distanceToCompactChapterTasteGate⟩, ⟨distanceToCompactFieldFaithful⟩,
      ⟨distanceToCompactNontrivial⟩, rfl, rfl, rfl,
      DistanceToCompactTasteGate_single_carrier_alignment_decode,
      DistanceToCompactTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq⟩

end BEDC.Derived.DistanceToCompactUp
