import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireOneFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireOneFunctionUp : Type where
  | mk (X F S Q R L H C P N : BHist) : BaireOneFunctionUp
  deriving DecidableEq

def baireOneFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireOneFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireOneFunctionEncodeBHist h

def baireOneFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireOneFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireOneFunctionDecodeBHist tail)

private theorem BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireOneFunctionFields : BaireOneFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireOneFunctionUp.mk X F S Q R L H C P N => [X, F, S, Q, R, L, H, C, P, N]

def baireOneFunctionToEventFlow : BaireOneFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireOneFunctionFields x).map baireOneFunctionEncodeBHist

private def baireOneFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireOneFunctionEventAt index rest

def baireOneFunctionFromEventFlow (ef : EventFlow) : Option BaireOneFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireOneFunctionUp.mk
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 0 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 1 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 2 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 3 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 4 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 5 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 6 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 7 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 8 ef))
      (baireOneFunctionDecodeBHist (baireOneFunctionEventAt 9 ef)))

private theorem BaireOneFunctionTasteGate_single_carrier_alignment_round_trip
    (x : BaireOneFunctionUp) :
    baireOneFunctionFromEventFlow (baireOneFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X F S Q R L H C P N =>
      change
        some
          (BaireOneFunctionUp.mk
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist X))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist F))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist S))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist Q))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist R))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist L))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist H))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist C))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist P))
            (baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist N))) =
          some (BaireOneFunctionUp.mk X F S Q R L H C P N)
      rw [BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode X,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode F,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode S,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode R,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode L,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode H,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode C,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode P,
        BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireOneFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireOneFunctionUp} :
    baireOneFunctionToEventFlow x = baireOneFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireOneFunctionFromEventFlow (baireOneFunctionToEventFlow x) =
        baireOneFunctionFromEventFlow (baireOneFunctionToEventFlow y) :=
    congrArg baireOneFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireOneFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireOneFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance baireOneFunctionBHistCarrier : BHistCarrier BaireOneFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireOneFunctionToEventFlow
  fromEventFlow := baireOneFunctionFromEventFlow

instance baireOneFunctionChapterTasteGate : ChapterTasteGate BaireOneFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireOneFunctionFromEventFlow (baireOneFunctionToEventFlow x) = some x
    exact BaireOneFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireOneFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def BaireOneFunctionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BaireOneFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireOneFunctionChapterTasteGate

theorem BaireOneFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, baireOneFunctionDecodeBHist (baireOneFunctionEncodeBHist h) = h) ∧
      (∀ x : BaireOneFunctionUp,
        baireOneFunctionFromEventFlow (baireOneFunctionToEventFlow x) = some x) ∧
        (∀ x y : BaireOneFunctionUp,
          baireOneFunctionToEventFlow x = baireOneFunctionToEventFlow y → x = y) ∧
          baireOneFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BaireOneFunctionTasteGate_single_carrier_alignment_decode_encode,
      BaireOneFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BaireOneFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BaireOneFunctionUp.TasteGate
