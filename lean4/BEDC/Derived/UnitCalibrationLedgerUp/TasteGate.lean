import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# UnitCalibrationLedgerUp TasteGate carrier.
-/

namespace BEDC.Derived.UnitCalibrationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnitCalibrationLedgerUp : Type where
  | mk (m u c e i r d k h p n : BHist) : UnitCalibrationLedgerUp
  deriving DecidableEq

private def unitCalibrationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unitCalibrationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unitCalibrationLedgerEncodeBHist h

private def unitCalibrationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unitCalibrationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unitCalibrationLedgerDecodeBHist tail)

private theorem unitCalibrationLedger_decode_encode_bhist :
    ∀ h : BHist,
      unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def unitCalibrationLedgerFields : UnitCalibrationLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnitCalibrationLedgerUp.mk m u c e i r d k h p n => [m, u, c, e, i, r, d, k, h, p, n]

private def unitCalibrationLedgerToEventFlow : UnitCalibrationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnitCalibrationLedgerUp.mk m u c e i r d k h p n =>
      [unitCalibrationLedgerEncodeBHist m, unitCalibrationLedgerEncodeBHist u,
        unitCalibrationLedgerEncodeBHist c, unitCalibrationLedgerEncodeBHist e,
        unitCalibrationLedgerEncodeBHist i, unitCalibrationLedgerEncodeBHist r,
        unitCalibrationLedgerEncodeBHist d, unitCalibrationLedgerEncodeBHist k,
        unitCalibrationLedgerEncodeBHist h, unitCalibrationLedgerEncodeBHist p,
        unitCalibrationLedgerEncodeBHist n]

private def unitCalibrationLedgerFromEventFlow : EventFlow → Option UnitCalibrationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [m, u, c, e, i, r, d, k, h, p, n] =>
      some
        (UnitCalibrationLedgerUp.mk
          (unitCalibrationLedgerDecodeBHist m)
          (unitCalibrationLedgerDecodeBHist u)
          (unitCalibrationLedgerDecodeBHist c)
          (unitCalibrationLedgerDecodeBHist e)
          (unitCalibrationLedgerDecodeBHist i)
          (unitCalibrationLedgerDecodeBHist r)
          (unitCalibrationLedgerDecodeBHist d)
          (unitCalibrationLedgerDecodeBHist k)
          (unitCalibrationLedgerDecodeBHist h)
          (unitCalibrationLedgerDecodeBHist p)
          (unitCalibrationLedgerDecodeBHist n))
  | _ => none

private theorem unitCalibrationLedger_round_trip :
    ∀ x : UnitCalibrationLedgerUp,
      unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk m u c e i r d k h p n =>
      change
        some
          (UnitCalibrationLedgerUp.mk
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist m))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist u))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist c))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist e))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist i))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist r))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist d))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist k))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist h))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist p))
            (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist n))) =
          some (UnitCalibrationLedgerUp.mk m u c e i r d k h p n)
      rw [unitCalibrationLedger_decode_encode_bhist m,
        unitCalibrationLedger_decode_encode_bhist u,
        unitCalibrationLedger_decode_encode_bhist c,
        unitCalibrationLedger_decode_encode_bhist e,
        unitCalibrationLedger_decode_encode_bhist i,
        unitCalibrationLedger_decode_encode_bhist r,
        unitCalibrationLedger_decode_encode_bhist d,
        unitCalibrationLedger_decode_encode_bhist k,
        unitCalibrationLedger_decode_encode_bhist h,
        unitCalibrationLedger_decode_encode_bhist p,
        unitCalibrationLedger_decode_encode_bhist n]

private theorem unitCalibrationLedgerToEventFlow_injective {x y : UnitCalibrationLedgerUp} :
    unitCalibrationLedgerToEventFlow x = unitCalibrationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) =
        unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow y) :=
    congrArg unitCalibrationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unitCalibrationLedger_round_trip x).symm
      (Eq.trans hread (unitCalibrationLedger_round_trip y)))

private theorem unitCalibrationLedger_field_faithful :
    ∀ x y : UnitCalibrationLedgerUp, unitCalibrationLedgerFields x =
      unitCalibrationLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk m u c e i r d k h p n =>
      cases y with
      | mk m' u' c' e' i' r' d' k' h' p' n' =>
          cases hfields
          rfl

instance unitCalibrationLedgerBHistCarrier : BHistCarrier UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unitCalibrationLedgerToEventFlow
  fromEventFlow := unitCalibrationLedgerFromEventFlow

instance unitCalibrationLedgerChapterTasteGate :
    ChapterTasteGate UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) = some x
    exact unitCalibrationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unitCalibrationLedgerToEventFlow_injective heq)

instance unitCalibrationLedgerFieldFaithful :
    FieldFaithful UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := unitCalibrationLedgerFields
  field_faithful := unitCalibrationLedger_field_faithful

instance unitCalibrationLedgerNontrivial :
    Nontrivial UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UnitCalibrationLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      UnitCalibrationLedgerUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UnitCalibrationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unitCalibrationLedgerChapterTasteGate

theorem UnitCalibrationLedgerTasteGate_single_carrier_alignment :
    ∀ m u c e i r d k h p n : BHist,
      unitCalibrationLedgerFields (UnitCalibrationLedgerUp.mk m u c e i r d k h p n) =
        [m, u, c, e, i, r, d, k, h, p, n] ∧
      unitCalibrationLedgerToEventFlow (UnitCalibrationLedgerUp.mk m u c e i r d k h p n) =
        [unitCalibrationLedgerEncodeBHist m, unitCalibrationLedgerEncodeBHist u,
          unitCalibrationLedgerEncodeBHist c, unitCalibrationLedgerEncodeBHist e,
          unitCalibrationLedgerEncodeBHist i, unitCalibrationLedgerEncodeBHist r,
          unitCalibrationLedgerEncodeBHist d, unitCalibrationLedgerEncodeBHist k,
          unitCalibrationLedgerEncodeBHist h, unitCalibrationLedgerEncodeBHist p,
          unitCalibrationLedgerEncodeBHist n] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro m u c e i r d k h p n
  constructor
  · rfl
  · rfl

end BEDC.Derived.UnitCalibrationLedgerUp
