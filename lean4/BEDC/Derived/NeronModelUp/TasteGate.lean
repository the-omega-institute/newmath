import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NeronModelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NeronModelUp : Type where
  | mk (K O G A eta U H C P N : BHist) : NeronModelUp
  deriving DecidableEq

def neronModelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: neronModelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: neronModelEncodeBHist h

def neronModelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (neronModelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (neronModelDecodeBHist tail)

private theorem neronModelDecode_encode_bhist :
    ∀ h : BHist, neronModelDecodeBHist (neronModelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def neronModelFields : NeronModelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NeronModelUp.mk K O G A eta U H C P N => [K, O, G, A, eta, U, H, C, P, N]

def neronModelToEventFlow : NeronModelUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (neronModelFields x).map neronModelEncodeBHist

private def neronModelEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => neronModelEventAtDefault index rest

def neronModelFromEventFlow (ef : EventFlow) : Option NeronModelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NeronModelUp.mk
      (neronModelDecodeBHist (neronModelEventAtDefault 0 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 1 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 2 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 3 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 4 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 5 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 6 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 7 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 8 ef))
      (neronModelDecodeBHist (neronModelEventAtDefault 9 ef)))

private theorem neronModel_round_trip :
    ∀ x : NeronModelUp, neronModelFromEventFlow (neronModelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K O G A eta U H C P N =>
      change
        some
          (NeronModelUp.mk
            (neronModelDecodeBHist (neronModelEncodeBHist K))
            (neronModelDecodeBHist (neronModelEncodeBHist O))
            (neronModelDecodeBHist (neronModelEncodeBHist G))
            (neronModelDecodeBHist (neronModelEncodeBHist A))
            (neronModelDecodeBHist (neronModelEncodeBHist eta))
            (neronModelDecodeBHist (neronModelEncodeBHist U))
            (neronModelDecodeBHist (neronModelEncodeBHist H))
            (neronModelDecodeBHist (neronModelEncodeBHist C))
            (neronModelDecodeBHist (neronModelEncodeBHist P))
            (neronModelDecodeBHist (neronModelEncodeBHist N))) =
          some (NeronModelUp.mk K O G A eta U H C P N)
      rw [neronModelDecode_encode_bhist K, neronModelDecode_encode_bhist O,
        neronModelDecode_encode_bhist G, neronModelDecode_encode_bhist A,
        neronModelDecode_encode_bhist eta, neronModelDecode_encode_bhist U,
        neronModelDecode_encode_bhist H, neronModelDecode_encode_bhist C,
        neronModelDecode_encode_bhist P, neronModelDecode_encode_bhist N]

private theorem neronModelToEventFlow_injective {x y : NeronModelUp} :
    neronModelToEventFlow x = neronModelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      neronModelFromEventFlow (neronModelToEventFlow x) =
        neronModelFromEventFlow (neronModelToEventFlow y) :=
    congrArg neronModelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (neronModel_round_trip x).symm
      (Eq.trans hread (neronModel_round_trip y)))

instance neronModelBHistCarrier : BHistCarrier NeronModelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := neronModelToEventFlow
  fromEventFlow := neronModelFromEventFlow

instance neronModelChapterTasteGate : ChapterTasteGate NeronModelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change neronModelFromEventFlow (neronModelToEventFlow x) = some x
    exact neronModel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (neronModelToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NeronModelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  neronModelChapterTasteGate

theorem NeronModelTasteGate_single_carrier_alignment :
    (∀ h : BHist, neronModelDecodeBHist (neronModelEncodeBHist h) = h) ∧
      (∀ x : NeronModelUp, neronModelFromEventFlow (neronModelToEventFlow x) = some x) ∧
        (∀ x y : NeronModelUp, neronModelToEventFlow x = neronModelToEventFlow y → x = y) ∧
          neronModelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨neronModelDecode_encode_bhist,
      ⟨neronModel_round_trip, ⟨fun _x _y heq => neronModelToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.NeronModelUp
