import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzModulusUp : Type where
  | mk (X Y F K E D U H C P N : BHist) : LipschitzModulusUp

def lipschitzModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzModulusEncodeBHist h

def lipschitzModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzModulusDecodeBHist tail)

private theorem LipschitzModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzModulusFields : LipschitzModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzModulusUp.mk X Y F K E D U H C P N => [X, Y, F, K, E, D, U, H, C, P, N]

def lipschitzModulusToEventFlow : LipschitzModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lipschitzModulusFields x).map lipschitzModulusEncodeBHist

private def lipschitzModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzModulusEventAt index rest

def lipschitzModulusFromEventFlow (ef : EventFlow) : Option LipschitzModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzModulusUp.mk
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 0 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 1 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 2 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 3 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 4 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 5 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 6 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 7 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 8 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 9 ef))
      (lipschitzModulusDecodeBHist (lipschitzModulusEventAt 10 ef)))

private theorem LipschitzModulusTasteGate_single_carrier_alignment_round_trip
    (x : LipschitzModulusUp) :
    lipschitzModulusFromEventFlow (lipschitzModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y F K E D U H C P N =>
      change
        some
          (LipschitzModulusUp.mk
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist X))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist Y))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist F))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist K))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist E))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist D))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist U))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist H))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist C))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist P))
            (lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist N))) =
          some (LipschitzModulusUp.mk X Y F K E D U H C P N)
      rw [LipschitzModulusTasteGate_single_carrier_alignment_decode_encode X,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode Y,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode F,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode K,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode E,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode D,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode U,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode H,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode C,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode P,
        LipschitzModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem lipschitzModulusToEventFlow_injective {x y : LipschitzModulusUp} :
    lipschitzModulusToEventFlow x = lipschitzModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzModulusFromEventFlow (lipschitzModulusToEventFlow x) =
        lipschitzModulusFromEventFlow (lipschitzModulusToEventFlow y) :=
    congrArg lipschitzModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LipschitzModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LipschitzModulusTasteGate_single_carrier_alignment_round_trip y)))

instance lipschitzModulusBHistCarrier : BHistCarrier LipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzModulusToEventFlow
  fromEventFlow := lipschitzModulusFromEventFlow

instance lipschitzModulusChapterTasteGate : ChapterTasteGate LipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzModulusFromEventFlow (lipschitzModulusToEventFlow x) = some x
    exact LipschitzModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lipschitzModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LipschitzModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lipschitzModulusChapterTasteGate

theorem LipschitzModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, lipschitzModulusDecodeBHist (lipschitzModulusEncodeBHist h) = h) ∧
      (∀ x : LipschitzModulusUp,
        lipschitzModulusFromEventFlow (lipschitzModulusToEventFlow x) = some x) ∧
        (∀ x y : LipschitzModulusUp,
          lipschitzModulusToEventFlow x = lipschitzModulusToEventFlow y → x = y) ∧
          lipschitzModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LipschitzModulusTasteGate_single_carrier_alignment_decode_encode,
      LipschitzModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => lipschitzModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LipschitzModulusUp
