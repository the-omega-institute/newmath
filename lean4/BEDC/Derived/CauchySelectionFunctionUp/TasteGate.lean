import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySelectionFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySelectionFunctionUp : Type where
  | mk (Q M W R D E H C P N : BHist) : CauchySelectionFunctionUp
  deriving DecidableEq

def cauchySelectionFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySelectionFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySelectionFunctionEncodeBHist h

def cauchySelectionFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySelectionFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySelectionFunctionDecodeBHist tail)

private theorem CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySelectionFunctionFields : CauchySelectionFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySelectionFunctionUp.mk Q M W R D E H C P N => [Q, M, W, R, D, E, H, C, P, N]

def cauchySelectionFunctionToEventFlow : CauchySelectionFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySelectionFunctionFields x).map cauchySelectionFunctionEncodeBHist

private def CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt index rest

def cauchySelectionFunctionFromEventFlow (ef : EventFlow) :
    Option CauchySelectionFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySelectionFunctionUp.mk
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchySelectionFunctionDecodeBHist
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CauchySelectionFunctionTasteGate_single_carrier_alignment_round_trip
    (x : CauchySelectionFunctionUp) :
    cauchySelectionFunctionFromEventFlow (cauchySelectionFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q M W R D E H C P N =>
      change
        some
          (CauchySelectionFunctionUp.mk
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist Q))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist M))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist W))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist R))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist D))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist E))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist H))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist C))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist P))
            (cauchySelectionFunctionDecodeBHist (cauchySelectionFunctionEncodeBHist N))) =
          some (CauchySelectionFunctionUp.mk Q M W R D E H C P N)
      rw [CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode M,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode W,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode R,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode D,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode E,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode H,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode C,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode P,
        CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySelectionFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySelectionFunctionUp} :
    cauchySelectionFunctionToEventFlow x = cauchySelectionFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySelectionFunctionFromEventFlow (cauchySelectionFunctionToEventFlow x) =
        cauchySelectionFunctionFromEventFlow (cauchySelectionFunctionToEventFlow y) :=
    congrArg cauchySelectionFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySelectionFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySelectionFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySelectionFunctionBHistCarrier : BHistCarrier CauchySelectionFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySelectionFunctionToEventFlow
  fromEventFlow := cauchySelectionFunctionFromEventFlow

instance cauchySelectionFunctionChapterTasteGate :
    ChapterTasteGate CauchySelectionFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySelectionFunctionFromEventFlow (cauchySelectionFunctionToEventFlow x) =
      some x
    exact CauchySelectionFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySelectionFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchySelectionFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySelectionFunctionDecodeBHist
        (cauchySelectionFunctionEncodeBHist h) = h) ∧
      (∀ x : CauchySelectionFunctionUp,
        cauchySelectionFunctionFromEventFlow
          (cauchySelectionFunctionToEventFlow x) = some x) ∧
        (∀ x y : CauchySelectionFunctionUp,
          cauchySelectionFunctionToEventFlow x =
            cauchySelectionFunctionToEventFlow y -> x = y) ∧
          cauchySelectionFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySelectionFunctionTasteGate_single_carrier_alignment_decode_encode,
      CauchySelectionFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchySelectionFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySelectionFunctionUp
