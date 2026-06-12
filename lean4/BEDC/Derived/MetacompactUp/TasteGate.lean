import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacompactUp : Type where
  | mk (T O R Q I S H C P N : BHist) : MetacompactUp
  deriving DecidableEq

def metacompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacompactEncodeBHist h

def metacompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacompactDecodeBHist tail)

private theorem metacompactDecodeEncodeBHist :
    ∀ h : BHist, metacompactDecodeBHist (metacompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metacompactFields : MetacompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetacompactUp.mk T O R Q I S H C P N => [T, O, R, Q, I, S, H, C, P, N]

def metacompactToEventFlow : MetacompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacompactFields x).map metacompactEncodeBHist

private def metacompactRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metacompactRawAt index rest

def metacompactFromEventFlow : EventFlow → Option MetacompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (MetacompactUp.mk
          (metacompactDecodeBHist (metacompactRawAt 0 flow))
          (metacompactDecodeBHist (metacompactRawAt 1 flow))
          (metacompactDecodeBHist (metacompactRawAt 2 flow))
          (metacompactDecodeBHist (metacompactRawAt 3 flow))
          (metacompactDecodeBHist (metacompactRawAt 4 flow))
          (metacompactDecodeBHist (metacompactRawAt 5 flow))
          (metacompactDecodeBHist (metacompactRawAt 6 flow))
          (metacompactDecodeBHist (metacompactRawAt 7 flow))
          (metacompactDecodeBHist (metacompactRawAt 8 flow))
          (metacompactDecodeBHist (metacompactRawAt 9 flow)))

private theorem metacompact_round_trip :
    ∀ x : MetacompactUp,
      metacompactFromEventFlow (metacompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T O R Q I S H C P N =>
      change
        some
          (MetacompactUp.mk
            (metacompactDecodeBHist (metacompactEncodeBHist T))
            (metacompactDecodeBHist (metacompactEncodeBHist O))
            (metacompactDecodeBHist (metacompactEncodeBHist R))
            (metacompactDecodeBHist (metacompactEncodeBHist Q))
            (metacompactDecodeBHist (metacompactEncodeBHist I))
            (metacompactDecodeBHist (metacompactEncodeBHist S))
            (metacompactDecodeBHist (metacompactEncodeBHist H))
            (metacompactDecodeBHist (metacompactEncodeBHist C))
            (metacompactDecodeBHist (metacompactEncodeBHist P))
            (metacompactDecodeBHist (metacompactEncodeBHist N))) =
          some (MetacompactUp.mk T O R Q I S H C P N)
      rw [metacompactDecodeEncodeBHist T, metacompactDecodeEncodeBHist O,
        metacompactDecodeEncodeBHist R, metacompactDecodeEncodeBHist Q,
        metacompactDecodeEncodeBHist I, metacompactDecodeEncodeBHist S,
        metacompactDecodeEncodeBHist H, metacompactDecodeEncodeBHist C,
        metacompactDecodeEncodeBHist P, metacompactDecodeEncodeBHist N]

private theorem metacompactToEventFlow_injective {x y : MetacompactUp} :
    metacompactToEventFlow x = metacompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacompactFromEventFlow (metacompactToEventFlow x) =
        metacompactFromEventFlow (metacompactToEventFlow y) :=
    congrArg metacompactFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (metacompact_round_trip x).symm
        (Eq.trans hread (metacompact_round_trip y)))

instance metacompactBHistCarrier : BHistCarrier MetacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacompactToEventFlow
  fromEventFlow := metacompactFromEventFlow

instance metacompactChapterTasteGate : ChapterTasteGate MetacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metacompactFromEventFlow (metacompactToEventFlow x) = some x
    exact metacompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacompactToEventFlow_injective heq)

theorem MetacompactTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacompactEncodeBHist (BHist.e0 h) = BMark.b0 :: metacompactEncodeBHist h) ∧
      (∀ h : BHist,
        metacompactEncodeBHist (BHist.e1 h) = BMark.b1 :: metacompactEncodeBHist h) ∧
        (∀ x : MetacompactUp,
          metacompactFromEventFlow (metacompactToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    rfl
  · constructor
    · intro h
      rfl
    · intro x
      exact metacompact_round_trip x

end BEDC.Derived.MetacompactUp
