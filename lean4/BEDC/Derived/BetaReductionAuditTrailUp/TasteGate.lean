import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaReductionAuditTrailUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaReductionAuditTrailUp : Type where
  | mk :
      (step conversion obstruction discharge transport route provenance nameCert : BHist) →
        BetaReductionAuditTrailUp
  deriving DecidableEq

def betaReductionAuditTrailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaReductionAuditTrailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaReductionAuditTrailEncodeBHist h

def betaReductionAuditTrailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaReductionAuditTrailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaReductionAuditTrailDecodeBHist tail)

private theorem betaReductionAuditTrail_decode_encode_bhist :
    ∀ h : BHist,
      betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def betaReductionAuditTrailToEventFlow : BetaReductionAuditTrailUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaReductionAuditTrailUp.mk step conversion obstruction discharge transport route provenance
      nameCert =>
      [[BMark.b0],
        betaReductionAuditTrailEncodeBHist step,
        [BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist conversion,
        [BMark.b1, BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist discharge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaReductionAuditTrailEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        betaReductionAuditTrailEncodeBHist nameCert]

private def betaReductionAuditTrailRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => betaReductionAuditTrailRawAt n rest

private def betaReductionAuditTrailLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => betaReductionAuditTrailLengthEq n rest

def betaReductionAuditTrailFromEventFlow : EventFlow → Option BetaReductionAuditTrailUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match betaReductionAuditTrailLengthEq 16 flow with
      | true =>
          some
            (BetaReductionAuditTrailUp.mk
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 1 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 3 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 5 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 7 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 9 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 11 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 13 flow))
              (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailRawAt 15 flow)))
      | false => none

private theorem betaReductionAuditTrail_round_trip :
    ∀ x : BetaReductionAuditTrailUp,
      betaReductionAuditTrailFromEventFlow (betaReductionAuditTrailToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk step conversion obstruction discharge transport route provenance nameCert =>
      change
        some
          (BetaReductionAuditTrailUp.mk
            (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailEncodeBHist step))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist conversion))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist obstruction))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist discharge))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist transport))
            (betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailEncodeBHist route))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist provenance))
            (betaReductionAuditTrailDecodeBHist
              (betaReductionAuditTrailEncodeBHist nameCert))) =
          some
            (BetaReductionAuditTrailUp.mk step conversion obstruction discharge transport route
              provenance nameCert)
      rw [betaReductionAuditTrail_decode_encode_bhist step,
        betaReductionAuditTrail_decode_encode_bhist conversion,
        betaReductionAuditTrail_decode_encode_bhist obstruction,
        betaReductionAuditTrail_decode_encode_bhist discharge,
        betaReductionAuditTrail_decode_encode_bhist transport,
        betaReductionAuditTrail_decode_encode_bhist route,
        betaReductionAuditTrail_decode_encode_bhist provenance,
        betaReductionAuditTrail_decode_encode_bhist nameCert]

private theorem betaReductionAuditTrailToEventFlow_injective
    {x y : BetaReductionAuditTrailUp} :
    betaReductionAuditTrailToEventFlow x = betaReductionAuditTrailToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaReductionAuditTrailFromEventFlow (betaReductionAuditTrailToEventFlow x) =
        betaReductionAuditTrailFromEventFlow (betaReductionAuditTrailToEventFlow y) :=
    congrArg betaReductionAuditTrailFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (betaReductionAuditTrail_round_trip x).symm
      (Eq.trans hread (betaReductionAuditTrail_round_trip y)))

instance betaReductionAuditTrailBHistCarrier : BHistCarrier BetaReductionAuditTrailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaReductionAuditTrailToEventFlow
  fromEventFlow := betaReductionAuditTrailFromEventFlow

instance betaReductionAuditTrailChapterTasteGate :
    ChapterTasteGate BetaReductionAuditTrailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change betaReductionAuditTrailFromEventFlow (betaReductionAuditTrailToEventFlow x) = some x
    exact betaReductionAuditTrail_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaReductionAuditTrailToEventFlow_injective heq)

instance betaReductionAuditTrailFieldFaithful : FieldFaithful BetaReductionAuditTrailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BetaReductionAuditTrailUp.mk step conversion obstruction discharge transport route
        provenance nameCert =>
        [step, conversion, obstruction, discharge, transport, route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk step1 conversion1 obstruction1 discharge1 transport1 route1 provenance1 nameCert1 =>
        cases y with
        | mk step2 conversion2 obstruction2 discharge2 transport2 route2 provenance2 nameCert2 =>
            cases h
            rfl

instance betaReductionAuditTrailNontrivial : Nontrivial BetaReductionAuditTrailUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BetaReductionAuditTrailUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BetaReductionAuditTrailUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BetaReductionAuditTrailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  betaReductionAuditTrailChapterTasteGate

theorem BetaReductionAuditTrailTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      betaReductionAuditTrailDecodeBHist (betaReductionAuditTrailEncodeBHist h) = h) ∧
      (∀ x : BetaReductionAuditTrailUp,
        betaReductionAuditTrailFromEventFlow (betaReductionAuditTrailToEventFlow x) = some x) ∧
        (∀ x y : BetaReductionAuditTrailUp,
          betaReductionAuditTrailToEventFlow x =
            betaReductionAuditTrailToEventFlow y → x = y) ∧
          betaReductionAuditTrailEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨betaReductionAuditTrail_decode_encode_bhist,
      betaReductionAuditTrail_round_trip,
      by
        intro x y heq
        exact betaReductionAuditTrailToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BetaReductionAuditTrailUp
