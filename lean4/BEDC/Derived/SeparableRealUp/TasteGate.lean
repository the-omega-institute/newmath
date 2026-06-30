import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparableRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparableRealUp : Type where
  | mk (D S R Q E H C P N : BHist) : SeparableRealUp
  deriving DecidableEq

def separableRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separableRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separableRealEncodeBHist h

def separableRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separableRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separableRealDecodeBHist tail)

private theorem SeparableRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, separableRealDecodeBHist (separableRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separableRealFields : SeparableRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableRealUp.mk D S R Q E H C P N => [D, S, R, Q, E, H, C, P, N]

def separableRealToEventFlow : SeparableRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (separableRealFields x).map separableRealEncodeBHist

private def separableRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separableRealEventAtDefault index rest

def separableRealFromEventFlow (ef : EventFlow) : Option SeparableRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparableRealUp.mk
      (separableRealDecodeBHist (separableRealEventAtDefault 0 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 1 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 2 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 3 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 4 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 5 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 6 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 7 ef))
      (separableRealDecodeBHist (separableRealEventAtDefault 8 ef)))

private theorem SeparableRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparableRealUp,
      separableRealFromEventFlow (separableRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R Q E H C P N =>
      change
        some
          (SeparableRealUp.mk
            (separableRealDecodeBHist (separableRealEncodeBHist D))
            (separableRealDecodeBHist (separableRealEncodeBHist S))
            (separableRealDecodeBHist (separableRealEncodeBHist R))
            (separableRealDecodeBHist (separableRealEncodeBHist Q))
            (separableRealDecodeBHist (separableRealEncodeBHist E))
            (separableRealDecodeBHist (separableRealEncodeBHist H))
            (separableRealDecodeBHist (separableRealEncodeBHist C))
            (separableRealDecodeBHist (separableRealEncodeBHist P))
            (separableRealDecodeBHist (separableRealEncodeBHist N))) =
          some (SeparableRealUp.mk D S R Q E H C P N)
      rw [SeparableRealTasteGate_single_carrier_alignment_decode D,
        SeparableRealTasteGate_single_carrier_alignment_decode S,
        SeparableRealTasteGate_single_carrier_alignment_decode R,
        SeparableRealTasteGate_single_carrier_alignment_decode Q,
        SeparableRealTasteGate_single_carrier_alignment_decode E,
        SeparableRealTasteGate_single_carrier_alignment_decode H,
        SeparableRealTasteGate_single_carrier_alignment_decode C,
        SeparableRealTasteGate_single_carrier_alignment_decode P,
        SeparableRealTasteGate_single_carrier_alignment_decode N]

private theorem separableRealToEventFlow_injective {x y : SeparableRealUp} :
    separableRealToEventFlow x = separableRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separableRealFromEventFlow (separableRealToEventFlow x) =
        separableRealFromEventFlow (separableRealToEventFlow y) :=
    congrArg separableRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeparableRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeparableRealTasteGate_single_carrier_alignment_round_trip y)))

instance separableRealBHistCarrier : BHistCarrier SeparableRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separableRealToEventFlow
  fromEventFlow := separableRealFromEventFlow

instance separableRealChapterTasteGate : ChapterTasteGate SeparableRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separableRealFromEventFlow (separableRealToEventFlow x) = some x
    exact SeparableRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separableRealToEventFlow_injective heq)

theorem SeparableRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, separableRealDecodeBHist (separableRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SeparableRealUp) ∧
        Nonempty (ChapterTasteGate SeparableRealUp) ∧
          separableRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SeparableRealTasteGate_single_carrier_alignment_decode,
      ⟨separableRealBHistCarrier⟩, ⟨separableRealChapterTasteGate⟩, rfl⟩

end BEDC.Derived.SeparableRealUp
