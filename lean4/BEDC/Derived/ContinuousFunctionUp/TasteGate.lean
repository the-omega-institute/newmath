import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousFunctionUp : Type where
  | mk (S T M Q W R H C P N : BHist) : ContinuousFunctionUp
  deriving DecidableEq

def continuousFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousFunctionEncodeBHist h

def continuousFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousFunctionDecodeBHist tail)

private theorem ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, continuousFunctionDecodeBHist (continuousFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuousFunctionFields : ContinuousFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousFunctionUp.mk S T M Q W R H C P N => [S, T, M, Q, W, R, H, C, P, N]

def continuousFunctionToEventFlow : ContinuousFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuousFunctionFields x).map continuousFunctionEncodeBHist

private def continuousFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuousFunctionEventAtDefault index rest

def continuousFunctionFromEventFlow (ef : EventFlow) : Option ContinuousFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousFunctionUp.mk
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 0 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 1 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 2 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 3 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 4 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 5 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 6 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 7 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 8 ef))
      (continuousFunctionDecodeBHist (continuousFunctionEventAtDefault 9 ef)))

private theorem ContinuousFunctionTasteGate_single_carrier_alignment_round_trip
    (x : ContinuousFunctionUp) :
    continuousFunctionFromEventFlow (continuousFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T M Q W R H C P N =>
      change
        some
          (ContinuousFunctionUp.mk
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist S))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist T))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist M))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist Q))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist W))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist R))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist H))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist C))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist P))
            (continuousFunctionDecodeBHist (continuousFunctionEncodeBHist N))) =
          some (ContinuousFunctionUp.mk S T M Q W R H C P N)
      rw [ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode S,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode T,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode M,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode W,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode R,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode H,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode C,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode P,
        ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ContinuousFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuousFunctionUp} :
    continuousFunctionToEventFlow x = continuousFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousFunctionFromEventFlow (continuousFunctionToEventFlow x) =
        continuousFunctionFromEventFlow (continuousFunctionToEventFlow y) :=
    congrArg continuousFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContinuousFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContinuousFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance continuousFunctionBHistCarrier : BHistCarrier ContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousFunctionToEventFlow
  fromEventFlow := continuousFunctionFromEventFlow

instance continuousFunctionChapterTasteGate : ChapterTasteGate ContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuousFunctionFromEventFlow (continuousFunctionToEventFlow x) = some x
    exact ContinuousFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContinuousFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContinuousFunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, continuousFunctionDecodeBHist (continuousFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ContinuousFunctionUp) ∧
      Nonempty (ChapterTasteGate ContinuousFunctionUp) ∧
      continuousFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ContinuousFunctionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨continuousFunctionBHistCarrier⟩
    · constructor
      · exact ⟨continuousFunctionChapterTasteGate⟩
      · rfl

end BEDC.Derived.ContinuousFunctionUp
