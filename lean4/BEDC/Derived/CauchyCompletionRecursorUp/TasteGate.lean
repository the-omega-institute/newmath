import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionRecursorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionRecursorUp : Type where
  | mk (S T f m E U H C P N : BHist) : CauchyCompletionRecursorUp
  deriving DecidableEq

def cauchyCompletionRecursorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionRecursorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionRecursorEncodeBHist h

def cauchyCompletionRecursorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionRecursorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionRecursorDecodeBHist tail)

private theorem cauchyCompletionRecursorDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionRecursorFields : CauchyCompletionRecursorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionRecursorUp.mk S T f m E U H C P N => [S, T, f, m, E, U, H, C, P, N]

def cauchyCompletionRecursorToEventFlow : CauchyCompletionRecursorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionRecursorFields x).map cauchyCompletionRecursorEncodeBHist

private def cauchyCompletionRecursorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionRecursorEventAt index rest

def cauchyCompletionRecursorFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionRecursorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionRecursorUp.mk
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 0 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 1 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 2 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 3 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 4 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 5 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 6 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 7 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 8 ef))
      (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEventAt 9 ef)))

private theorem cauchyCompletionRecursor_round_trip (x : CauchyCompletionRecursorUp) :
    cauchyCompletionRecursorFromEventFlow (cauchyCompletionRecursorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T f m E U H C P N =>
      change
        some
          (CauchyCompletionRecursorUp.mk
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist S))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist T))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist f))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist m))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist E))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist U))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist H))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist C))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist P))
            (cauchyCompletionRecursorDecodeBHist (cauchyCompletionRecursorEncodeBHist N))) =
          some (CauchyCompletionRecursorUp.mk S T f m E U H C P N)
      rw [cauchyCompletionRecursorDecode_encode_bhist S,
        cauchyCompletionRecursorDecode_encode_bhist T,
        cauchyCompletionRecursorDecode_encode_bhist f,
        cauchyCompletionRecursorDecode_encode_bhist m,
        cauchyCompletionRecursorDecode_encode_bhist E,
        cauchyCompletionRecursorDecode_encode_bhist U,
        cauchyCompletionRecursorDecode_encode_bhist H,
        cauchyCompletionRecursorDecode_encode_bhist C,
        cauchyCompletionRecursorDecode_encode_bhist P,
        cauchyCompletionRecursorDecode_encode_bhist N]

private theorem cauchyCompletionRecursorToEventFlow_injective
    {x y : CauchyCompletionRecursorUp} :
    cauchyCompletionRecursorToEventFlow x = cauchyCompletionRecursorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionRecursorFromEventFlow (cauchyCompletionRecursorToEventFlow x) =
        cauchyCompletionRecursorFromEventFlow (cauchyCompletionRecursorToEventFlow y) :=
    congrArg cauchyCompletionRecursorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionRecursor_round_trip x).symm
      (Eq.trans hread (cauchyCompletionRecursor_round_trip y)))

instance cauchyCompletionRecursorBHistCarrier : BHistCarrier CauchyCompletionRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionRecursorToEventFlow
  fromEventFlow := cauchyCompletionRecursorFromEventFlow

instance cauchyCompletionRecursorChapterTasteGate :
    ChapterTasteGate CauchyCompletionRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionRecursorFromEventFlow
      (cauchyCompletionRecursorToEventFlow x) = some x
    exact cauchyCompletionRecursor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionRecursorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionRecursorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionRecursorChapterTasteGate

theorem CauchyCompletionRecursorTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyCompletionRecursorUp) ∧
      Nonempty (ChapterTasteGate CauchyCompletionRecursorUp) ∧
        ∀ x y : CauchyCompletionRecursorUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyCompletionRecursorBHistCarrier⟩
  · constructor
    · exact ⟨cauchyCompletionRecursorChapterTasteGate⟩
    · intro x y heq
      change cauchyCompletionRecursorToEventFlow x =
        cauchyCompletionRecursorToEventFlow y at heq
      exact cauchyCompletionRecursorToEventFlow_injective heq

end BEDC.Derived.CauchyCompletionRecursorUp
