import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CookCompileFrontierWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CookCompileFrontierWitnessUp : Type where
  | mk :
      (stage coordinate audit obstruction transport route provenance name : BHist) →
      CookCompileFrontierWitnessUp
  deriving DecidableEq

def cookCompileFrontierWitnessEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cookCompileFrontierWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cookCompileFrontierWitnessEncodeBHist h

def cookCompileFrontierWitnessDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cookCompileFrontierWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cookCompileFrontierWitnessDecodeBHist tail)

private theorem cookCompileFrontierWitnessDecode_encode_bhist :
    ∀ h : BHist,
      cookCompileFrontierWitnessDecodeBHist
        (cookCompileFrontierWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cookCompileFrontierWitnessToEventFlow :
    CookCompileFrontierWitnessUp → EventFlow
  | CookCompileFrontierWitnessUp.mk stage coordinate audit obstruction transport route
      provenance name =>
      [[BMark.b0],
        cookCompileFrontierWitnessEncodeBHist stage,
        [BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist coordinate,
        [BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookCompileFrontierWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cookCompileFrontierWitnessEncodeBHist name]

private def cookCompileFrontierWitnessRawAt : Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cookCompileFrontierWitnessRawAt n rest

private def cookCompileFrontierWitnessLengthEq : Nat → EventFlow → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cookCompileFrontierWitnessLengthEq n rest

private def cookCompileFrontierWitnessFromEventFlow :
    EventFlow → Option CookCompileFrontierWitnessUp
  | flow =>
      match cookCompileFrontierWitnessLengthEq 16 flow with
      | true =>
          some
            (CookCompileFrontierWitnessUp.mk
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 1 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 3 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 5 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 7 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 9 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 11 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 13 flow))
              (cookCompileFrontierWitnessDecodeBHist
                (cookCompileFrontierWitnessRawAt 15 flow)))
      | false => none

private theorem cookCompileFrontierWitness_round_trip :
    ∀ x : CookCompileFrontierWitnessUp,
      cookCompileFrontierWitnessFromEventFlow
        (cookCompileFrontierWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stage coordinate audit obstruction transport route provenance name =>
      change
        some
          (CookCompileFrontierWitnessUp.mk
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist stage))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist coordinate))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist audit))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist obstruction))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist transport))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist route))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist provenance))
            (cookCompileFrontierWitnessDecodeBHist
              (cookCompileFrontierWitnessEncodeBHist name))) =
          some
            (CookCompileFrontierWitnessUp.mk stage coordinate audit obstruction transport
              route provenance name)
      let mkCongr
          {stage' coordinate' audit' obstruction' transport' route' provenance' name' :
            BHist}
          (hStage : stage' = stage)
          (hCoordinate : coordinate' = coordinate)
          (hAudit : audit' = audit)
          (hObstruction : obstruction' = obstruction)
          (hTransport : transport' = transport)
          (hRoute : route' = route)
          (hProvenance : provenance' = provenance)
          (hName : name' = name) :
          CookCompileFrontierWitnessUp.mk stage' coordinate' audit' obstruction'
              transport' route' provenance' name' =
            CookCompileFrontierWitnessUp.mk stage coordinate audit obstruction transport
              route provenance name := by
        cases hStage
        cases hCoordinate
        cases hAudit
        cases hObstruction
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hName
        rfl
      exact
        congrArg some
          (mkCongr
            (cookCompileFrontierWitnessDecode_encode_bhist stage)
            (cookCompileFrontierWitnessDecode_encode_bhist coordinate)
            (cookCompileFrontierWitnessDecode_encode_bhist audit)
            (cookCompileFrontierWitnessDecode_encode_bhist obstruction)
            (cookCompileFrontierWitnessDecode_encode_bhist transport)
            (cookCompileFrontierWitnessDecode_encode_bhist route)
            (cookCompileFrontierWitnessDecode_encode_bhist provenance)
            (cookCompileFrontierWitnessDecode_encode_bhist name))

private theorem cookCompileFrontierWitnessToEventFlow_injective
    {x y : CookCompileFrontierWitnessUp} :
    cookCompileFrontierWitnessToEventFlow x =
      cookCompileFrontierWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cookCompileFrontierWitnessFromEventFlow
          (cookCompileFrontierWitnessToEventFlow x) =
        cookCompileFrontierWitnessFromEventFlow
          (cookCompileFrontierWitnessToEventFlow y) :=
    congrArg cookCompileFrontierWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cookCompileFrontierWitness_round_trip x).symm
      (Eq.trans hread (cookCompileFrontierWitness_round_trip y)))

instance cookCompileFrontierWitnessBHistCarrier :
    BHistCarrier CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cookCompileFrontierWitnessToEventFlow
  fromEventFlow := cookCompileFrontierWitnessFromEventFlow

instance cookCompileFrontierWitnessChapterTasteGate :
    ChapterTasteGate CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cookCompileFrontierWitnessFromEventFlow
          (cookCompileFrontierWitnessToEventFlow x) =
        some x
    exact cookCompileFrontierWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cookCompileFrontierWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CookCompileFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cookCompileFrontierWitnessChapterTasteGate

instance cookCompileFrontierWitnessNontrivial :
    Nontrivial CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CookCompileFrontierWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CookCompileFrontierWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def cookCompileFrontierWitnessFields :
    CookCompileFrontierWitnessUp → List BHist
  | CookCompileFrontierWitnessUp.mk stage coordinate audit obstruction transport route
      provenance name =>
      [stage, coordinate, audit, obstruction, transport, route, provenance, name]

private theorem cookCompileFrontierWitness_field_faithful_concrete :
    ∀ x y : CookCompileFrontierWitnessUp,
      cookCompileFrontierWitnessFields x =
        cookCompileFrontierWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stage coordinate audit obstruction transport route provenance name =>
      cases y with
      | mk stage' coordinate' audit' obstruction' transport' route' provenance' name' =>
          injection hfields with hStage hTail0
          injection hTail0 with hCoordinate hTail1
          injection hTail1 with hAudit hTail2
          injection hTail2 with hObstruction hTail3
          injection hTail3 with hTransport hTail4
          injection hTail4 with hRoute hTail5
          injection hTail5 with hProvenance hTail6
          injection hTail6 with hName _hNil
          cases hStage
          cases hCoordinate
          cases hAudit
          cases hObstruction
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance cookCompileFrontierWitnessFieldFaithful :
    FieldFaithful CookCompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cookCompileFrontierWitnessFields
  field_faithful := cookCompileFrontierWitness_field_faithful_concrete

end BEDC.Derived.CookCompileFrontierWitnessUp
