import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KraftPrefixCodeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KraftPrefixCodeUp : Type where
  | mk (row : BHist) : KraftPrefixCodeUp
  deriving DecidableEq

def kraftPrefixCodeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kraftPrefixCodeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kraftPrefixCodeEncodeBHist h

def kraftPrefixCodeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kraftPrefixCodeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kraftPrefixCodeDecodeBHist tail)

private theorem kraftPrefixCode_decode_encode_bhist :
    ∀ h : BHist, kraftPrefixCodeDecodeBHist (kraftPrefixCodeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kraftPrefixCodeToEventFlow : KraftPrefixCodeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KraftPrefixCodeUp.mk row => [kraftPrefixCodeEncodeBHist row]

def kraftPrefixCodeFromEventFlow : EventFlow → Option KraftPrefixCodeUp
  -- BEDC touchpoint anchor: BHist BMark
  | event :: _rest => some (KraftPrefixCodeUp.mk (kraftPrefixCodeDecodeBHist event))
  | [] => some (KraftPrefixCodeUp.mk BHist.Empty)

private theorem kraftPrefixCode_round_trip (x : KraftPrefixCodeUp) :
    kraftPrefixCodeFromEventFlow (kraftPrefixCodeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk row =>
      change
        some (KraftPrefixCodeUp.mk
          (kraftPrefixCodeDecodeBHist (kraftPrefixCodeEncodeBHist row))) =
            some (KraftPrefixCodeUp.mk row)
      rw [kraftPrefixCode_decode_encode_bhist row]

private theorem kraftPrefixCodeToEventFlow_injective {x y : KraftPrefixCodeUp} :
    kraftPrefixCodeToEventFlow x = kraftPrefixCodeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kraftPrefixCodeFromEventFlow (kraftPrefixCodeToEventFlow x) =
        kraftPrefixCodeFromEventFlow (kraftPrefixCodeToEventFlow y) :=
    congrArg kraftPrefixCodeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kraftPrefixCode_round_trip x).symm
      (Eq.trans hread (kraftPrefixCode_round_trip y)))

instance kraftPrefixCodeBHistCarrier : BHistCarrier KraftPrefixCodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kraftPrefixCodeToEventFlow
  fromEventFlow := kraftPrefixCodeFromEventFlow

instance kraftPrefixCodeChapterTasteGate : ChapterTasteGate KraftPrefixCodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kraftPrefixCodeFromEventFlow (kraftPrefixCodeToEventFlow x) = some x
    exact kraftPrefixCode_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kraftPrefixCodeToEventFlow_injective heq)

theorem KraftPrefixCodeTasteGate_single_carrier_alignment :
    (∀ h : BHist, kraftPrefixCodeDecodeBHist (kraftPrefixCodeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KraftPrefixCodeUp) ∧
        Nonempty (ChapterTasteGate KraftPrefixCodeUp) ∧
          kraftPrefixCodeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · intro h
    exact kraftPrefixCode_decode_encode_bhist h
  · constructor
    · exact ⟨kraftPrefixCodeBHistCarrier⟩
    · constructor
      · exact ⟨kraftPrefixCodeChapterTasteGate⟩
      · rfl

end BEDC.Derived.KraftPrefixCodeUp
