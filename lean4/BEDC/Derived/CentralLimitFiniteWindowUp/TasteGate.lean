import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CentralLimitFiniteWindowUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CentralLimitFiniteWindowUp : Type where
  | mk (P V S K D R E H C Q N : BHist) : CentralLimitFiniteWindowUp
  deriving DecidableEq

def centralLimitFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: centralLimitFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: centralLimitFiniteWindowEncodeBHist h

def centralLimitFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (centralLimitFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (centralLimitFiniteWindowDecodeBHist tail)

private theorem centralLimitFiniteWindowDecode_encode_bhist :
    ∀ h : BHist,
      centralLimitFiniteWindowDecodeBHist
        (centralLimitFiniteWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def centralLimitFiniteWindowFields : CentralLimitFiniteWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CentralLimitFiniteWindowUp.mk P V S K D R E H C Q N => [P, V, S, K, D, R, E, H, C, Q, N]

def centralLimitFiniteWindowToEventFlow : CentralLimitFiniteWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (centralLimitFiniteWindowFields x).map centralLimitFiniteWindowEncodeBHist

private def centralLimitFiniteWindowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => centralLimitFiniteWindowEventAt index rest

def centralLimitFiniteWindowFromEventFlow (ef : EventFlow) :
    Option CentralLimitFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CentralLimitFiniteWindowUp.mk
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 0 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 1 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 2 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 3 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 4 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 5 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 6 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 7 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 8 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 9 ef))
      (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEventAt 10 ef)))

private theorem centralLimitFiniteWindow_round_trip (x : CentralLimitFiniteWindowUp) :
    centralLimitFiniteWindowFromEventFlow
        (centralLimitFiniteWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P V S K D R E H C Q N =>
      change
        some
          (CentralLimitFiniteWindowUp.mk
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist P))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist V))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist S))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist K))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist D))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist R))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist E))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist H))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist C))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist Q))
            (centralLimitFiniteWindowDecodeBHist (centralLimitFiniteWindowEncodeBHist N))) =
          some (CentralLimitFiniteWindowUp.mk P V S K D R E H C Q N)
      rw [centralLimitFiniteWindowDecode_encode_bhist P,
        centralLimitFiniteWindowDecode_encode_bhist V,
        centralLimitFiniteWindowDecode_encode_bhist S,
        centralLimitFiniteWindowDecode_encode_bhist K,
        centralLimitFiniteWindowDecode_encode_bhist D,
        centralLimitFiniteWindowDecode_encode_bhist R,
        centralLimitFiniteWindowDecode_encode_bhist E,
        centralLimitFiniteWindowDecode_encode_bhist H,
        centralLimitFiniteWindowDecode_encode_bhist C,
        centralLimitFiniteWindowDecode_encode_bhist Q,
        centralLimitFiniteWindowDecode_encode_bhist N]

private theorem centralLimitFiniteWindowToEventFlow_injective
    {x y : CentralLimitFiniteWindowUp} :
    centralLimitFiniteWindowToEventFlow x =
      centralLimitFiniteWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      centralLimitFiniteWindowFromEventFlow (centralLimitFiniteWindowToEventFlow x) =
        centralLimitFiniteWindowFromEventFlow (centralLimitFiniteWindowToEventFlow y) :=
    congrArg centralLimitFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (centralLimitFiniteWindow_round_trip x).symm
      (Eq.trans hread (centralLimitFiniteWindow_round_trip y)))

instance centralLimitFiniteWindowBHistCarrier :
    BHistCarrier CentralLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := centralLimitFiniteWindowToEventFlow
  fromEventFlow := centralLimitFiniteWindowFromEventFlow

instance centralLimitFiniteWindowChapterTasteGate :
    ChapterTasteGate CentralLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      centralLimitFiniteWindowFromEventFlow
          (centralLimitFiniteWindowToEventFlow x) =
        some x
    exact centralLimitFiniteWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (centralLimitFiniteWindowToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CentralLimitFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  centralLimitFiniteWindowChapterTasteGate

theorem CentralLimitFiniteWindowTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CentralLimitFiniteWindowUp) ∧
      Nonempty (ChapterTasteGate CentralLimitFiniteWindowUp) ∧
        (∀ h : BHist,
          centralLimitFiniteWindowDecodeBHist
              (centralLimitFiniteWindowEncodeBHist h) = h) ∧
          (∀ x : CentralLimitFiniteWindowUp,
            centralLimitFiniteWindowFromEventFlow
                (centralLimitFiniteWindowToEventFlow x) = some x) ∧
            centralLimitFiniteWindowEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨centralLimitFiniteWindowBHistCarrier⟩
  · constructor
    · exact ⟨centralLimitFiniteWindowChapterTasteGate⟩
    · constructor
      · exact centralLimitFiniteWindowDecode_encode_bhist
      · constructor
        · exact centralLimitFiniteWindow_round_trip
        · rfl

end BEDC.Derived.CentralLimitFiniteWindowUp.TasteGate
