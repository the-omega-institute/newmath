import BEDC.Derived.MarkedRealUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MarkedRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def markedRealEncodeBHist : BEDC.FKernel.Hist.BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: markedRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: markedRealEncodeBHist h

def markedRealDecodeBHist : RawEvent → BEDC.FKernel.Hist.BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (markedRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (markedRealDecodeBHist tail)

private theorem MarkedRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BEDC.FKernel.Hist.BHist, markedRealDecodeBHist (markedRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def markedRealFields : BEDC.Derived.MarkedRealUp → List BEDC.FKernel.Hist.BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.MarkedRealUp.mk R S A L Z Pm Nm Q H C K N =>
      [R, S, A, L, Z, Pm, Nm, Q, H, C, K, N]

def markedRealToEventFlow : BEDC.Derived.MarkedRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (markedRealFields x).map markedRealEncodeBHist

private def markedRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => markedRealEventAtDefault index rest

def markedRealFromEventFlow (ef : EventFlow) : Option BEDC.Derived.MarkedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.MarkedRealUp.mk
      (markedRealDecodeBHist (markedRealEventAtDefault 0 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 1 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 2 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 3 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 4 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 5 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 6 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 7 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 8 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 9 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 10 ef))
      (markedRealDecodeBHist (markedRealEventAtDefault 11 ef)))

private theorem MarkedRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.MarkedRealUp,
      markedRealFromEventFlow (markedRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S A L Z Pm Nm Q H C K N =>
      change
        some
          (BEDC.Derived.MarkedRealUp.mk
            (markedRealDecodeBHist (markedRealEncodeBHist R))
            (markedRealDecodeBHist (markedRealEncodeBHist S))
            (markedRealDecodeBHist (markedRealEncodeBHist A))
            (markedRealDecodeBHist (markedRealEncodeBHist L))
            (markedRealDecodeBHist (markedRealEncodeBHist Z))
            (markedRealDecodeBHist (markedRealEncodeBHist Pm))
            (markedRealDecodeBHist (markedRealEncodeBHist Nm))
            (markedRealDecodeBHist (markedRealEncodeBHist Q))
            (markedRealDecodeBHist (markedRealEncodeBHist H))
            (markedRealDecodeBHist (markedRealEncodeBHist C))
            (markedRealDecodeBHist (markedRealEncodeBHist K))
            (markedRealDecodeBHist (markedRealEncodeBHist N))) =
          some (BEDC.Derived.MarkedRealUp.mk R S A L Z Pm Nm Q H C K N)
      rw [MarkedRealTasteGate_single_carrier_alignment_decode R,
        MarkedRealTasteGate_single_carrier_alignment_decode S,
        MarkedRealTasteGate_single_carrier_alignment_decode A,
        MarkedRealTasteGate_single_carrier_alignment_decode L,
        MarkedRealTasteGate_single_carrier_alignment_decode Z,
        MarkedRealTasteGate_single_carrier_alignment_decode Pm,
        MarkedRealTasteGate_single_carrier_alignment_decode Nm,
        MarkedRealTasteGate_single_carrier_alignment_decode Q,
        MarkedRealTasteGate_single_carrier_alignment_decode H,
        MarkedRealTasteGate_single_carrier_alignment_decode C,
        MarkedRealTasteGate_single_carrier_alignment_decode K,
        MarkedRealTasteGate_single_carrier_alignment_decode N]

private theorem MarkedRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.MarkedRealUp} :
    markedRealToEventFlow x = markedRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      markedRealFromEventFlow (markedRealToEventFlow x) =
        markedRealFromEventFlow (markedRealToEventFlow y) :=
    congrArg markedRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MarkedRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MarkedRealTasteGate_single_carrier_alignment_round_trip y)))

instance markedRealBHistCarrier : BHistCarrier BEDC.Derived.MarkedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := markedRealToEventFlow
  fromEventFlow := markedRealFromEventFlow

instance markedRealChapterTasteGate : ChapterTasteGate BEDC.Derived.MarkedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change markedRealFromEventFlow (markedRealToEventFlow x) = some x
    exact MarkedRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MarkedRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.MarkedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  markedRealChapterTasteGate

theorem MarkedRealTasteGate_single_carrier_alignment :
    (∀ h : BEDC.FKernel.Hist.BHist,
        markedRealDecodeBHist (markedRealEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.MarkedRealUp,
        markedRealFromEventFlow (markedRealToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.MarkedRealUp,
          markedRealToEventFlow x = markedRealToEventFlow y → x = y) ∧
          markedRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MarkedRealTasteGate_single_carrier_alignment_decode,
      MarkedRealTasteGate_single_carrier_alignment_round_trip,
      fun x y hxy => MarkedRealTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.MarkedRealUp
