import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LieGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LieGroupUp : Type where
  | mk (carrier classifier mul inv unit chart atlas smooth transport replay provenance name : BHist) :
      LieGroupUp
  deriving DecidableEq

def lieGroupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lieGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lieGroupEncodeBHist h

def lieGroupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lieGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lieGroupDecodeBHist tail)

private theorem LieGroupTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lieGroupDecodeBHist (lieGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lieGroupFields : LieGroupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LieGroupUp.mk carrier classifier mul inv unit chart atlas smooth transport replay provenance name =>
      [carrier, classifier, mul, inv, unit, chart, atlas, smooth, transport, replay,
        provenance, name]

def lieGroupToEventFlow : LieGroupUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lieGroupFields x).map lieGroupEncodeBHist

private def lieGroupEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lieGroupEventAtDefault index rest

def lieGroupFromEventFlow (ef : EventFlow) : Option LieGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LieGroupUp.mk
      (lieGroupDecodeBHist (lieGroupEventAtDefault 0 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 1 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 2 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 3 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 4 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 5 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 6 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 7 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 8 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 9 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 10 ef))
      (lieGroupDecodeBHist (lieGroupEventAtDefault 11 ef)))

private theorem LieGroupTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LieGroupUp, lieGroupFromEventFlow (lieGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk carrier classifier mul inv unit chart atlas smooth transport replay provenance name =>
      change
        some
          (LieGroupUp.mk
            (lieGroupDecodeBHist (lieGroupEncodeBHist carrier))
            (lieGroupDecodeBHist (lieGroupEncodeBHist classifier))
            (lieGroupDecodeBHist (lieGroupEncodeBHist mul))
            (lieGroupDecodeBHist (lieGroupEncodeBHist inv))
            (lieGroupDecodeBHist (lieGroupEncodeBHist unit))
            (lieGroupDecodeBHist (lieGroupEncodeBHist chart))
            (lieGroupDecodeBHist (lieGroupEncodeBHist atlas))
            (lieGroupDecodeBHist (lieGroupEncodeBHist smooth))
            (lieGroupDecodeBHist (lieGroupEncodeBHist transport))
            (lieGroupDecodeBHist (lieGroupEncodeBHist replay))
            (lieGroupDecodeBHist (lieGroupEncodeBHist provenance))
            (lieGroupDecodeBHist (lieGroupEncodeBHist name))) =
          some
            (LieGroupUp.mk carrier classifier mul inv unit chart atlas smooth transport replay
              provenance name)
      rw [LieGroupTasteGate_single_carrier_alignment_decode carrier,
        LieGroupTasteGate_single_carrier_alignment_decode classifier,
        LieGroupTasteGate_single_carrier_alignment_decode mul,
        LieGroupTasteGate_single_carrier_alignment_decode inv,
        LieGroupTasteGate_single_carrier_alignment_decode unit,
        LieGroupTasteGate_single_carrier_alignment_decode chart,
        LieGroupTasteGate_single_carrier_alignment_decode atlas,
        LieGroupTasteGate_single_carrier_alignment_decode smooth,
        LieGroupTasteGate_single_carrier_alignment_decode transport,
        LieGroupTasteGate_single_carrier_alignment_decode replay,
        LieGroupTasteGate_single_carrier_alignment_decode provenance,
        LieGroupTasteGate_single_carrier_alignment_decode name]

private theorem LieGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LieGroupUp} :
    lieGroupToEventFlow x = lieGroupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lieGroupFromEventFlow (lieGroupToEventFlow x) =
        lieGroupFromEventFlow (lieGroupToEventFlow y) :=
    congrArg lieGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LieGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LieGroupTasteGate_single_carrier_alignment_round_trip y)))

instance lieGroupBHistCarrier : BHistCarrier LieGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lieGroupToEventFlow
  fromEventFlow := lieGroupFromEventFlow

instance lieGroupChapterTasteGate : ChapterTasteGate LieGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lieGroupFromEventFlow (lieGroupToEventFlow x) = some x
    exact LieGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LieGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LieGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lieGroupChapterTasteGate

theorem LieGroupTasteGate_single_carrier_alignment :
    (∀ h : BHist, lieGroupDecodeBHist (lieGroupEncodeBHist h) = h) ∧
      (∀ x : LieGroupUp, lieGroupFromEventFlow (lieGroupToEventFlow x) = some x) ∧
        (∀ x y : LieGroupUp, lieGroupToEventFlow x = lieGroupToEventFlow y → x = y) ∧
          lieGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LieGroupTasteGate_single_carrier_alignment_decode,
      LieGroupTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LieGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LieGroupUp
