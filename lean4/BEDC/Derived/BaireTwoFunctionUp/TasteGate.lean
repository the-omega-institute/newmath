import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireTwoFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireTwoFunctionUp : Type where
  | mk (B A S Q R H C P N : BHist) : BaireTwoFunctionUp
  deriving DecidableEq

def baireTwoFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireTwoFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireTwoFunctionEncodeBHist h

def baireTwoFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireTwoFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireTwoFunctionDecodeBHist tail)

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BaireTwoFunctionTasteGate_single_carrier_alignment_fields :
    BaireTwoFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireTwoFunctionUp.mk B A S Q R H C P N => [B, A, S, Q, R, H, C, P, N]

def baireTwoFunctionToEventFlow : BaireTwoFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (BaireTwoFunctionTasteGate_single_carrier_alignment_fields x).map
      baireTwoFunctionEncodeBHist

private def baireTwoFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireTwoFunctionEventAt index rest

def baireTwoFunctionFromEventFlow (ef : EventFlow) : Option BaireTwoFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireTwoFunctionUp.mk
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 0 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 1 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 2 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 3 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 4 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 5 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 6 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 7 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 8 ef)))

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip
    (x : BaireTwoFunctionUp) :
    baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B A S Q R H C P N =>
      change
        some
          (BaireTwoFunctionUp.mk
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist B))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist A))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist S))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist Q))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist R))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist H))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist C))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist P))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist N))) =
          some (BaireTwoFunctionUp.mk B A S Q R H C P N)
      rw [BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode B,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode A,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode S,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode R,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode H,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode C,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode P,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireTwoFunctionUp} :
    baireTwoFunctionToEventFlow x = baireTwoFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) =
        baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow y) :=
    congrArg baireTwoFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance baireTwoFunctionBHistCarrier : BHistCarrier BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireTwoFunctionToEventFlow
  fromEventFlow := baireTwoFunctionFromEventFlow

instance baireTwoFunctionChapterTasteGate : ChapterTasteGate BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x
    exact BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BaireTwoFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist h) = h) ∧
      (∀ x : BaireTwoFunctionUp,
        baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x) ∧
        (∀ x y : BaireTwoFunctionUp,
          baireTwoFunctionToEventFlow x = baireTwoFunctionToEventFlow y → x = y) ∧
          baireTwoFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BaireTwoFunctionTasteGate_single_carrier_alignment_decode_encode,
      BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BaireTwoFunctionUp
