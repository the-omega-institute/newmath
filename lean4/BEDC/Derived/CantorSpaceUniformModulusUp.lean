import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorSpaceUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorSpaceUniformModulusUp : Type where
  | mk (F A B S D R U E H C P N : BHist) : CantorSpaceUniformModulusUp
  deriving DecidableEq

def cantorSpaceUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorSpaceUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorSpaceUniformModulusEncodeBHist h

def cantorSpaceUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorSpaceUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorSpaceUniformModulusDecodeBHist tail)

private theorem CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorSpaceUniformModulusFields : CantorSpaceUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorSpaceUniformModulusUp.mk F A B S D R U E H C P N =>
      [F, A, B, S, D, R, U, E, H, C, P, N]

def cantorSpaceUniformModulusToEventFlow : CantorSpaceUniformModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cantorSpaceUniformModulusFields x).map cantorSpaceUniformModulusEncodeBHist

private def cantorSpaceUniformModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorSpaceUniformModulusEventAtDefault index rest

def cantorSpaceUniformModulusFromEventFlow
    (ef : EventFlow) : Option CantorSpaceUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorSpaceUniformModulusUp.mk
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 0 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 1 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 2 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 3 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 4 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 5 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 6 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 7 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 8 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 9 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 10 ef))
      (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEventAtDefault 11 ef)))

private theorem CantorSpaceUniformModulusTasteGate_single_carrier_alignment_round_trip
    (x : CantorSpaceUniformModulusUp) :
    cantorSpaceUniformModulusFromEventFlow (cantorSpaceUniformModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F A B S D R U E H C P N =>
      change
        some
          (CantorSpaceUniformModulusUp.mk
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist F))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist A))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist B))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist S))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist D))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist R))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist U))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist E))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist H))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist C))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist P))
            (cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist N))) =
          some (CantorSpaceUniformModulusUp.mk F A B S D R U E H C P N)
      rw [CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode F,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode A,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode B,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode S,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode D,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode R,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode U,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode E,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode H,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode C,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode P,
        CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem CantorSpaceUniformModulusToEventFlow_injective
    {x y : CantorSpaceUniformModulusUp} :
    cantorSpaceUniformModulusToEventFlow x = cantorSpaceUniformModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorSpaceUniformModulusFromEventFlow (cantorSpaceUniformModulusToEventFlow x) =
        cantorSpaceUniformModulusFromEventFlow (cantorSpaceUniformModulusToEventFlow y) :=
    congrArg cantorSpaceUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorSpaceUniformModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CantorSpaceUniformModulusTasteGate_single_carrier_alignment_round_trip y)))

instance cantorSpaceUniformModulusBHistCarrier :
    BHistCarrier CantorSpaceUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorSpaceUniformModulusToEventFlow
  fromEventFlow := cantorSpaceUniformModulusFromEventFlow

instance cantorSpaceUniformModulusChapterTasteGate :
    ChapterTasteGate CantorSpaceUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cantorSpaceUniformModulusFromEventFlow (cantorSpaceUniformModulusToEventFlow x) =
        some x
    exact CantorSpaceUniformModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorSpaceUniformModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CantorSpaceUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorSpaceUniformModulusChapterTasteGate

theorem CantorSpaceUniformModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cantorSpaceUniformModulusDecodeBHist (cantorSpaceUniformModulusEncodeBHist h) = h) ∧
      (∀ x : CantorSpaceUniformModulusUp,
        cantorSpaceUniformModulusFromEventFlow (cantorSpaceUniformModulusToEventFlow x) =
          some x) ∧
        (∀ x y : CantorSpaceUniformModulusUp,
          cantorSpaceUniformModulusToEventFlow x = cantorSpaceUniformModulusToEventFlow y →
            x = y) ∧
          cantorSpaceUniformModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CantorSpaceUniformModulusTasteGate_single_carrier_alignment_decode_encode,
      CantorSpaceUniformModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CantorSpaceUniformModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorSpaceUniformModulusUp
