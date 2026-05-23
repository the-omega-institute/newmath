import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingObstructionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingObstructionUp : Type where
  | mk :
      (cert input trace self policy transport route provenance name : BHist) →
      HaltingObstructionUp
  deriving DecidableEq

def haltingObstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingObstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingObstructionEncodeBHist h

def haltingObstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingObstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingObstructionDecodeBHist tail)

private theorem haltingObstructionDecode_encode_bhist :
    ∀ h : BHist, haltingObstructionDecodeBHist (haltingObstructionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem haltingObstruction_mk_congr
    {cert cert' input input' trace trace' self self' policy policy'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hCert : cert' = cert)
    (hInput : input' = input)
    (hTrace : trace' = trace)
    (hSelf : self' = self)
    (hPolicy : policy' = policy)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    HaltingObstructionUp.mk cert' input' trace' self' policy' transport' route' provenance' name' =
      HaltingObstructionUp.mk cert input trace self policy transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCert
  cases hInput
  cases hTrace
  cases hSelf
  cases hPolicy
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def haltingObstructionToEventFlow : HaltingObstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingObstructionUp.mk cert input trace self policy transport route provenance name =>
      [haltingObstructionEncodeBHist cert,
        haltingObstructionEncodeBHist input,
        haltingObstructionEncodeBHist trace,
        haltingObstructionEncodeBHist self,
        haltingObstructionEncodeBHist policy,
        haltingObstructionEncodeBHist transport,
        haltingObstructionEncodeBHist route,
        haltingObstructionEncodeBHist provenance,
        haltingObstructionEncodeBHist name]

def haltingObstructionFromEventFlow : EventFlow → Option HaltingObstructionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [cert, input, trace, self, policy, transport, route, provenance, name] =>
      some
        (HaltingObstructionUp.mk
          (haltingObstructionDecodeBHist cert)
          (haltingObstructionDecodeBHist input)
          (haltingObstructionDecodeBHist trace)
          (haltingObstructionDecodeBHist self)
          (haltingObstructionDecodeBHist policy)
          (haltingObstructionDecodeBHist transport)
          (haltingObstructionDecodeBHist route)
          (haltingObstructionDecodeBHist provenance)
          (haltingObstructionDecodeBHist name))
  | _ => none

private theorem haltingObstruction_round_trip :
    ∀ x : HaltingObstructionUp,
      haltingObstructionFromEventFlow (haltingObstructionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk cert input trace self policy transport route provenance name =>
      exact
        congrArg some
          (haltingObstruction_mk_congr
            (haltingObstructionDecode_encode_bhist cert)
            (haltingObstructionDecode_encode_bhist input)
            (haltingObstructionDecode_encode_bhist trace)
            (haltingObstructionDecode_encode_bhist self)
            (haltingObstructionDecode_encode_bhist policy)
            (haltingObstructionDecode_encode_bhist transport)
            (haltingObstructionDecode_encode_bhist route)
            (haltingObstructionDecode_encode_bhist provenance)
            (haltingObstructionDecode_encode_bhist name))

private theorem haltingObstructionToEventFlow_injective {x y : HaltingObstructionUp} :
    haltingObstructionToEventFlow x = haltingObstructionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingObstructionFromEventFlow (haltingObstructionToEventFlow x) =
        haltingObstructionFromEventFlow (haltingObstructionToEventFlow y) :=
    congrArg haltingObstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingObstruction_round_trip x).symm
      (Eq.trans hread (haltingObstruction_round_trip y)))

instance haltingObstructionBHistCarrier : BHistCarrier HaltingObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingObstructionToEventFlow
  fromEventFlow := haltingObstructionFromEventFlow

instance haltingObstructionChapterTasteGate :
    ChapterTasteGate HaltingObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingObstructionFromEventFlow (haltingObstructionToEventFlow x) = some x
    exact haltingObstruction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingObstructionToEventFlow_injective heq)

theorem HaltingObstructionTasteGate_single_carrier_alignment :
    (∀ h : BHist, haltingObstructionDecodeBHist (haltingObstructionEncodeBHist h) = h) ∧
      (∀ cert input trace self policy transport route provenance name : BHist,
        haltingObstructionToEventFlow
            (HaltingObstructionUp.mk cert input trace self policy transport route provenance name) =
          [haltingObstructionEncodeBHist cert,
            haltingObstructionEncodeBHist input,
            haltingObstructionEncodeBHist trace,
            haltingObstructionEncodeBHist self,
            haltingObstructionEncodeBHist policy,
            haltingObstructionEncodeBHist transport,
            haltingObstructionEncodeBHist route,
            haltingObstructionEncodeBHist provenance,
            haltingObstructionEncodeBHist name]) ∧
        ∀ cert input trace self policy transport route provenance name : BHist,
          HaltingObstructionUp.mk cert input trace self policy transport route provenance name =
            HaltingObstructionUp.mk cert input trace self policy transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact haltingObstructionDecode_encode_bhist
  · constructor
    · intro cert input trace self policy transport route provenance name
      rfl
    · intro cert input trace self policy transport route provenance name
      rfl

end BEDC.Derived.HaltingObstructionUp
