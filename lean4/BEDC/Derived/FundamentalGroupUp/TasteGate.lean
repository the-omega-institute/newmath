import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FundamentalGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FundamentalGroupUp : Type where
  | mk (X x0 L Q M I E U H C P N : BHist) : FundamentalGroupUp
  deriving DecidableEq

def fundamentalGroupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fundamentalGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fundamentalGroupEncodeBHist h

def fundamentalGroupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fundamentalGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fundamentalGroupDecodeBHist tail)

private theorem FundamentalGroupTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fundamentalGroupFields : FundamentalGroupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FundamentalGroupUp.mk X x0 L Q M I E U H C P N => [X, x0, L, Q, M, I, E, U, H, C, P, N]

def fundamentalGroupToEventFlow : FundamentalGroupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fundamentalGroupFields x).map fundamentalGroupEncodeBHist

private def fundamentalGroupEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fundamentalGroupEventAt index rest

def fundamentalGroupFromEventFlow (ef : EventFlow) : Option FundamentalGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FundamentalGroupUp.mk
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 0 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 1 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 2 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 3 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 4 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 5 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 6 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 7 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 8 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 9 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 10 ef))
      (fundamentalGroupDecodeBHist (fundamentalGroupEventAt 11 ef)))

private theorem FundamentalGroupTasteGate_single_carrier_alignment_round_trip
    (x : FundamentalGroupUp) :
    fundamentalGroupFromEventFlow (fundamentalGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X x0 L Q M I E U H C P N =>
      change
        some
          (FundamentalGroupUp.mk
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist X))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist x0))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist L))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist Q))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist M))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist I))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist E))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist U))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist H))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist C))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist P))
            (fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist N))) =
          some (FundamentalGroupUp.mk X x0 L Q M I E U H C P N)
      rw [FundamentalGroupTasteGate_single_carrier_alignment_decode_encode X,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode x0,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode L,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode Q,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode M,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode I,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode E,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode U,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode H,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode C,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode P,
        FundamentalGroupTasteGate_single_carrier_alignment_decode_encode N]

private theorem FundamentalGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FundamentalGroupUp} :
    fundamentalGroupToEventFlow x = fundamentalGroupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fundamentalGroupFromEventFlow (fundamentalGroupToEventFlow x) =
        fundamentalGroupFromEventFlow (fundamentalGroupToEventFlow y) :=
    congrArg fundamentalGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FundamentalGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FundamentalGroupTasteGate_single_carrier_alignment_round_trip y)))

instance fundamentalGroupBHistCarrier : BHistCarrier FundamentalGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fundamentalGroupToEventFlow
  fromEventFlow := fundamentalGroupFromEventFlow

instance fundamentalGroupChapterTasteGate : ChapterTasteGate FundamentalGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fundamentalGroupFromEventFlow (fundamentalGroupToEventFlow x) = some x
    exact FundamentalGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FundamentalGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FundamentalGroupTasteGate_single_carrier_alignment :
    (∀ h : BHist, fundamentalGroupDecodeBHist (fundamentalGroupEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FundamentalGroupUp) ∧
      Nonempty (ChapterTasteGate FundamentalGroupUp) ∧
      fundamentalGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FundamentalGroupTasteGate_single_carrier_alignment_decode_encode,
      ⟨fundamentalGroupBHistCarrier⟩, ⟨fundamentalGroupChapterTasteGate⟩, rfl⟩

end BEDC.Derived.FundamentalGroupUp
