import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedFunctionCompactOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedFunctionCompactOscillationUp : Type where
  | mk (F W M O D Q R H C P N : BHist) : RegulatedFunctionCompactOscillationUp

def regulatedFunctionCompactOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedFunctionCompactOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedFunctionCompactOscillationEncodeBHist h

def regulatedFunctionCompactOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedFunctionCompactOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedFunctionCompactOscillationDecodeBHist tail)

private theorem RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedFunctionCompactOscillationFields :
    RegulatedFunctionCompactOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedFunctionCompactOscillationUp.mk F W M O D Q R H C P N =>
      [F, W, M, O, D, Q, R, H, C, P, N]

def regulatedFunctionCompactOscillationToEventFlow :
    RegulatedFunctionCompactOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regulatedFunctionCompactOscillationFields x).map
        regulatedFunctionCompactOscillationEncodeBHist

private def regulatedFunctionCompactOscillationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regulatedFunctionCompactOscillationEventAtDefault index rest

def regulatedFunctionCompactOscillationFromEventFlow
    (ef : EventFlow) : Option RegulatedFunctionCompactOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegulatedFunctionCompactOscillationUp.mk
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 0 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 1 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 2 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 3 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 4 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 5 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 6 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 7 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 8 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 9 ef))
      (regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEventAtDefault 10 ef)))

private theorem RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_round_trip
    (x : RegulatedFunctionCompactOscillationUp) :
    regulatedFunctionCompactOscillationFromEventFlow
      (regulatedFunctionCompactOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F W M O D Q R H C P N =>
      change
        some
          (RegulatedFunctionCompactOscillationUp.mk
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist F))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist W))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist M))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist O))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist D))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist Q))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist R))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist H))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist C))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist P))
            (regulatedFunctionCompactOscillationDecodeBHist
              (regulatedFunctionCompactOscillationEncodeBHist N))) =
          some (RegulatedFunctionCompactOscillationUp.mk F W M O D Q R H C P N)
      rw [RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode F,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode W,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode M,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode O,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode D,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode Q,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode R,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode H,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode C,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode P,
        RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedFunctionCompactOscillationUp} :
    regulatedFunctionCompactOscillationToEventFlow x =
        regulatedFunctionCompactOscillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedFunctionCompactOscillationFromEventFlow
          (regulatedFunctionCompactOscillationToEventFlow x) =
        regulatedFunctionCompactOscillationFromEventFlow
          (regulatedFunctionCompactOscillationToEventFlow y) :=
    congrArg regulatedFunctionCompactOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedFunctionCompactOscillationBHistCarrier :
    BHistCarrier RegulatedFunctionCompactOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedFunctionCompactOscillationToEventFlow
  fromEventFlow := regulatedFunctionCompactOscillationFromEventFlow

instance regulatedFunctionCompactOscillationChapterTasteGate :
    ChapterTasteGate RegulatedFunctionCompactOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedFunctionCompactOscillationFromEventFlow
      (regulatedFunctionCompactOscillationToEventFlow x) = some x
    exact RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate RegulatedFunctionCompactOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedFunctionCompactOscillationChapterTasteGate

theorem RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regulatedFunctionCompactOscillationDecodeBHist
        (regulatedFunctionCompactOscillationEncodeBHist h) = h) ∧
      (∀ x : RegulatedFunctionCompactOscillationUp,
        regulatedFunctionCompactOscillationFromEventFlow
          (regulatedFunctionCompactOscillationToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier RegulatedFunctionCompactOscillationUp) ∧
          Nonempty (ChapterTasteGate RegulatedFunctionCompactOscillationUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_decode,
      RegulatedFunctionCompactOscillationTasteGate_single_carrier_alignment_round_trip,
      ⟨regulatedFunctionCompactOscillationBHistCarrier⟩,
      ⟨regulatedFunctionCompactOscillationChapterTasteGate⟩⟩

end BEDC.Derived.RegulatedFunctionCompactOscillationUp
