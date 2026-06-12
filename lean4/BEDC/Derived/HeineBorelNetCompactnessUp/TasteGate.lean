import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelNetCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelNetCompactnessUp : Type where
  | mk (I F R W D E H C P N : BHist) : HeineBorelNetCompactnessUp
  deriving DecidableEq

def heineBorelNetCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelNetCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelNetCompactnessEncodeBHist h

def heineBorelNetCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelNetCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelNetCompactnessDecodeBHist tail)

private theorem heineBorelNetCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelNetCompactnessFields : HeineBorelNetCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelNetCompactnessUp.mk I F R W D E H C P N => [I, F, R, W, D, E, H, C, P, N]

def heineBorelNetCompactnessToEventFlow : HeineBorelNetCompactnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (heineBorelNetCompactnessFields x).map heineBorelNetCompactnessEncodeBHist

private def heineBorelNetCompactnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heineBorelNetCompactnessEventAt index rest

def heineBorelNetCompactnessFromEventFlow
    (ef : EventFlow) : Option HeineBorelNetCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HeineBorelNetCompactnessUp.mk
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 0 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 1 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 2 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 3 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 4 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 5 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 6 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 7 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 8 ef))
      (heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEventAt 9 ef)))

private theorem heineBorelNetCompactness_round_trip
    (x : HeineBorelNetCompactnessUp) :
    heineBorelNetCompactnessFromEventFlow (heineBorelNetCompactnessToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F R W D E H C P N =>
      change
        some
          (HeineBorelNetCompactnessUp.mk
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist I))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist F))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist R))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist W))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist D))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist E))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist H))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist C))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist P))
            (heineBorelNetCompactnessDecodeBHist
              (heineBorelNetCompactnessEncodeBHist N))) =
          some (HeineBorelNetCompactnessUp.mk I F R W D E H C P N)
      rw [heineBorelNetCompactnessDecode_encode_bhist I,
        heineBorelNetCompactnessDecode_encode_bhist F,
        heineBorelNetCompactnessDecode_encode_bhist R,
        heineBorelNetCompactnessDecode_encode_bhist W,
        heineBorelNetCompactnessDecode_encode_bhist D,
        heineBorelNetCompactnessDecode_encode_bhist E,
        heineBorelNetCompactnessDecode_encode_bhist H,
        heineBorelNetCompactnessDecode_encode_bhist C,
        heineBorelNetCompactnessDecode_encode_bhist P,
        heineBorelNetCompactnessDecode_encode_bhist N]

private theorem heineBorelNetCompactnessToEventFlow_injective
    {x y : HeineBorelNetCompactnessUp} :
    heineBorelNetCompactnessToEventFlow x =
        heineBorelNetCompactnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelNetCompactnessFromEventFlow (heineBorelNetCompactnessToEventFlow x) =
        heineBorelNetCompactnessFromEventFlow (heineBorelNetCompactnessToEventFlow y) :=
    congrArg heineBorelNetCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (heineBorelNetCompactness_round_trip x).symm
      (Eq.trans hread (heineBorelNetCompactness_round_trip y)))

instance heineBorelNetCompactnessBHistCarrier :
    BHistCarrier HeineBorelNetCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelNetCompactnessToEventFlow
  fromEventFlow := heineBorelNetCompactnessFromEventFlow

instance heineBorelNetCompactnessChapterTasteGate :
    ChapterTasteGate HeineBorelNetCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      heineBorelNetCompactnessFromEventFlow (heineBorelNetCompactnessToEventFlow x) =
        some x
    exact heineBorelNetCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (heineBorelNetCompactnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HeineBorelNetCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelNetCompactnessChapterTasteGate

theorem HeineBorelNetCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      heineBorelNetCompactnessDecodeBHist (heineBorelNetCompactnessEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier HeineBorelNetCompactnessUp) ∧
        Nonempty (ChapterTasteGate HeineBorelNetCompactnessUp) ∧
          heineBorelNetCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨heineBorelNetCompactnessDecode_encode_bhist,
      ⟨heineBorelNetCompactnessBHistCarrier⟩,
      ⟨heineBorelNetCompactnessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HeineBorelNetCompactnessUp
