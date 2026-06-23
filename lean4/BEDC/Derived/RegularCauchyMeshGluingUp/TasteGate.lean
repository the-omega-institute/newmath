import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMeshGluingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMeshGluingUp : Type where
  | mk (M G Q B S R D E H C P N : BHist) : RegularCauchyMeshGluingUp
  deriving DecidableEq

def regularCauchyMeshGluingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMeshGluingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMeshGluingEncodeBHist h

def regularCauchyMeshGluingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMeshGluingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMeshGluingDecodeBHist tail)

private theorem RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMeshGluingToEventFlow : RegularCauchyMeshGluingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMeshGluingUp.mk M G Q B S R D E H C P N =>
      [regularCauchyMeshGluingEncodeBHist M,
        regularCauchyMeshGluingEncodeBHist G,
        regularCauchyMeshGluingEncodeBHist Q,
        regularCauchyMeshGluingEncodeBHist B,
        regularCauchyMeshGluingEncodeBHist S,
        regularCauchyMeshGluingEncodeBHist R,
        regularCauchyMeshGluingEncodeBHist D,
        regularCauchyMeshGluingEncodeBHist E,
        regularCauchyMeshGluingEncodeBHist H,
        regularCauchyMeshGluingEncodeBHist C,
        regularCauchyMeshGluingEncodeBHist P,
        regularCauchyMeshGluingEncodeBHist N]

private def regularCauchyMeshGluingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMeshGluingEventAtDefault index rest

def regularCauchyMeshGluingFromEventFlow
    (ef : EventFlow) : Option RegularCauchyMeshGluingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMeshGluingUp.mk
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 0 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 1 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 2 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 3 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 4 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 5 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 6 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 7 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 8 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 9 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 10 ef))
      (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEventAtDefault 11 ef)))

private theorem RegularCauchyMeshGluingTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyMeshGluingUp) :
    regularCauchyMeshGluingFromEventFlow (regularCauchyMeshGluingToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M G Q B S R D E H C P N =>
      change
        some
          (RegularCauchyMeshGluingUp.mk
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist M))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist G))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist Q))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist B))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist S))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist R))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist D))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist E))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist H))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist C))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist P))
            (regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist N))) =
          some (RegularCauchyMeshGluingUp.mk M G Q B S R D E H C P N)
      rw [RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode G,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyMeshGluingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMeshGluingUp} :
    regularCauchyMeshGluingToEventFlow x =
      regularCauchyMeshGluingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMeshGluingFromEventFlow (regularCauchyMeshGluingToEventFlow x) =
        regularCauchyMeshGluingFromEventFlow (regularCauchyMeshGluingToEventFlow y) :=
    congrArg regularCauchyMeshGluingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMeshGluingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyMeshGluingTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMeshGluingBHistCarrier : BHistCarrier RegularCauchyMeshGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMeshGluingToEventFlow
  fromEventFlow := regularCauchyMeshGluingFromEventFlow

instance regularCauchyMeshGluingChapterTasteGate :
    ChapterTasteGate RegularCauchyMeshGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMeshGluingFromEventFlow (regularCauchyMeshGluingToEventFlow x) =
      some x
    exact RegularCauchyMeshGluingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMeshGluingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyMeshGluingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyMeshGluingDecodeBHist (regularCauchyMeshGluingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyMeshGluingUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyMeshGluingUp) ∧
          regularCauchyMeshGluingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyMeshGluingTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyMeshGluingBHistCarrier⟩,
      ⟨regularCauchyMeshGluingChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyMeshGluingUp
