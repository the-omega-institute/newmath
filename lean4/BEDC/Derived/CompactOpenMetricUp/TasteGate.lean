import BEDC.Derived.CompactOpenMetricUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOpenMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactOpenMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOpenMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOpenMetricEncodeBHist h

def compactOpenMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOpenMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOpenMetricDecodeBHist tail)

private theorem CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOpenMetricFields : CompactOpenMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOpenMetricUp.mk X Y F G M D S H C P N => [X, Y, F, G, M, D, S, H, C, P, N]

def compactOpenMetricToEventFlow : CompactOpenMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactOpenMetricFields x).map compactOpenMetricEncodeBHist

def compactOpenMetricFromEventFlow : EventFlow → Option CompactOpenMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _Y :: [] => none
  | _X :: _Y :: _F :: [] => none
  | _X :: _Y :: _F :: _G :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: _D :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: _D :: _S :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: _D :: _S :: _H :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: _D :: _S :: _H :: _C :: [] => none
  | _X :: _Y :: _F :: _G :: _M :: _D :: _S :: _H :: _C :: _P :: [] => none
  | X :: Y :: F :: G :: M :: D :: S :: H :: C :: P :: N :: [] =>
      some
        (CompactOpenMetricUp.mk
          (compactOpenMetricDecodeBHist X)
          (compactOpenMetricDecodeBHist Y)
          (compactOpenMetricDecodeBHist F)
          (compactOpenMetricDecodeBHist G)
          (compactOpenMetricDecodeBHist M)
          (compactOpenMetricDecodeBHist D)
          (compactOpenMetricDecodeBHist S)
          (compactOpenMetricDecodeBHist H)
          (compactOpenMetricDecodeBHist C)
          (compactOpenMetricDecodeBHist P)
          (compactOpenMetricDecodeBHist N))
  | _X :: _Y :: _F :: _G :: _M :: _D :: _S :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem CompactOpenMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactOpenMetricUp,
      compactOpenMetricFromEventFlow (compactOpenMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F G M D S H C P N =>
      change
        some
          (CompactOpenMetricUp.mk
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist X))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist Y))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist F))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist G))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist M))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist D))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist S))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist H))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist C))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist P))
            (compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist N))) =
          some (CompactOpenMetricUp.mk X Y F G M D S H C P N)
      rw [CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode X,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode Y,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode F,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode G,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode M,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode D,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode S,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode H,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode C,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode P,
        CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactOpenMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactOpenMetricUp} :
    compactOpenMetricToEventFlow x = compactOpenMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOpenMetricFromEventFlow (compactOpenMetricToEventFlow x) =
        compactOpenMetricFromEventFlow (compactOpenMetricToEventFlow y) :=
    congrArg compactOpenMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactOpenMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactOpenMetricTasteGate_single_carrier_alignment_round_trip y)))

instance compactOpenMetricBHistCarrier : BHistCarrier CompactOpenMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOpenMetricToEventFlow
  fromEventFlow := compactOpenMetricFromEventFlow

instance compactOpenMetricChapterTasteGate : ChapterTasteGate CompactOpenMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactOpenMetricFromEventFlow (compactOpenMetricToEventFlow x) = some x
    exact CompactOpenMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactOpenMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOpenMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOpenMetricChapterTasteGate

theorem CompactOpenMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactOpenMetricDecodeBHist (compactOpenMetricEncodeBHist h) = h) ∧
      (∀ x : CompactOpenMetricUp,
        compactOpenMetricFromEventFlow (compactOpenMetricToEventFlow x) = some x) ∧
        (∀ x y : CompactOpenMetricUp,
          compactOpenMetricToEventFlow x = compactOpenMetricToEventFlow y → x = y) ∧
          compactOpenMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactOpenMetricTasteGate_single_carrier_alignment_decode_encode,
      CompactOpenMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactOpenMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactOpenMetricUp
