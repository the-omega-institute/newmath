import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveSobolevEnergyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveSobolevEnergyUp : Type where
  | mk (F D E A B H C P N : BHist) : ConstructiveSobolevEnergyUp
  deriving DecidableEq

def constructiveSobolevEnergyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveSobolevEnergyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveSobolevEnergyEncodeBHist h

def constructiveSobolevEnergyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveSobolevEnergyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveSobolevEnergyDecodeBHist tail)

private theorem ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveSobolevEnergyFields : ConstructiveSobolevEnergyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveSobolevEnergyUp.mk F D E A B H C P N => [F, D, E, A, B, H, C, P, N]

def constructiveSobolevEnergyToEventFlow : ConstructiveSobolevEnergyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveSobolevEnergyFields x).map constructiveSobolevEnergyEncodeBHist

private def constructiveSobolevEnergyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveSobolevEnergyEventAt index rest

def constructiveSobolevEnergyFromEventFlow (ef : EventFlow) :
    Option ConstructiveSobolevEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveSobolevEnergyUp.mk
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 0 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 1 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 2 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 3 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 4 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 5 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 6 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 7 ef))
      (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEventAt 8 ef)))

private theorem ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveSobolevEnergyUp) :
    constructiveSobolevEnergyFromEventFlow (constructiveSobolevEnergyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F D E A B H C P N =>
      change
        some
          (ConstructiveSobolevEnergyUp.mk
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist F))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist D))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist E))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist A))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist B))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist H))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist C))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist P))
            (constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist N))) =
          some (ConstructiveSobolevEnergyUp.mk F D E A B H C P N)
      rw [ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode D,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode A,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode B,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveSobolevEnergyUp} :
    constructiveSobolevEnergyToEventFlow x = constructiveSobolevEnergyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveSobolevEnergyFromEventFlow (constructiveSobolevEnergyToEventFlow x) =
        constructiveSobolevEnergyFromEventFlow (constructiveSobolevEnergyToEventFlow y) :=
    congrArg constructiveSobolevEnergyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveSobolevEnergyBHistCarrier :
    BHistCarrier ConstructiveSobolevEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveSobolevEnergyToEventFlow
  fromEventFlow := constructiveSobolevEnergyFromEventFlow

instance constructiveSobolevEnergyChapterTasteGate :
    ChapterTasteGate ConstructiveSobolevEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveSobolevEnergyFromEventFlow
      (constructiveSobolevEnergyToEventFlow x) = some x
    exact ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ConstructiveSobolevEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveSobolevEnergyChapterTasteGate

theorem ConstructiveSobolevEnergyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveSobolevEnergyDecodeBHist (constructiveSobolevEnergyEncodeBHist h) = h) ∧
      (∀ x : ConstructiveSobolevEnergyUp,
        constructiveSobolevEnergyFromEventFlow
          (constructiveSobolevEnergyToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveSobolevEnergyUp,
          constructiveSobolevEnergyToEventFlow x =
            constructiveSobolevEnergyToEventFlow y → x = y) ∧
          constructiveSobolevEnergyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_decode_encode,
      ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveSobolevEnergyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConstructiveSobolevEnergyUp
