import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyApproximationSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyApproximationSequenceUp : Type where
  | mk (Q D S R E H C P N : BHist) : CauchyApproximationSequenceUp
  deriving DecidableEq

def cauchyApproximationSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyApproximationSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyApproximationSequenceEncodeBHist h

def cauchyApproximationSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyApproximationSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyApproximationSequenceDecodeBHist tail)

private theorem CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyApproximationSequenceDecodeBHist
        (cauchyApproximationSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyApproximationSequenceFields : CauchyApproximationSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationSequenceUp.mk Q D S R E H C P N => [Q, D, S, R, E, H, C, P, N]

def cauchyApproximationSequenceToEventFlow : CauchyApproximationSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyApproximationSequenceFields x).map cauchyApproximationSequenceEncodeBHist

private def cauchyApproximationSequenceDecodePacket
    (Q D S R E H C P N : RawEvent) : CauchyApproximationSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyApproximationSequenceUp.mk
    (cauchyApproximationSequenceDecodeBHist Q)
    (cauchyApproximationSequenceDecodeBHist D)
    (cauchyApproximationSequenceDecodeBHist S)
    (cauchyApproximationSequenceDecodeBHist R)
    (cauchyApproximationSequenceDecodeBHist E)
    (cauchyApproximationSequenceDecodeBHist H)
    (cauchyApproximationSequenceDecodeBHist C)
    (cauchyApproximationSequenceDecodeBHist P)
    (cauchyApproximationSequenceDecodeBHist N)

private def cauchyApproximationSequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyApproximationSequenceRawAt n rest

private def cauchyApproximationSequenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyApproximationSequenceLengthEq n rest

def cauchyApproximationSequenceFromEventFlow
    (flow : EventFlow) : Option CauchyApproximationSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match cauchyApproximationSequenceLengthEq 9 flow with
  | true =>
      some
        (cauchyApproximationSequenceDecodePacket
          (cauchyApproximationSequenceRawAt 0 flow)
          (cauchyApproximationSequenceRawAt 1 flow)
          (cauchyApproximationSequenceRawAt 2 flow)
          (cauchyApproximationSequenceRawAt 3 flow)
          (cauchyApproximationSequenceRawAt 4 flow)
          (cauchyApproximationSequenceRawAt 5 flow)
          (cauchyApproximationSequenceRawAt 6 flow)
          (cauchyApproximationSequenceRawAt 7 flow)
          (cauchyApproximationSequenceRawAt 8 flow))
  | false => none

private theorem CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyApproximationSequenceUp,
      cauchyApproximationSequenceFromEventFlow
        (cauchyApproximationSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S R E H C P N =>
      change
        some
          (cauchyApproximationSequenceDecodePacket
            (cauchyApproximationSequenceEncodeBHist Q)
            (cauchyApproximationSequenceEncodeBHist D)
            (cauchyApproximationSequenceEncodeBHist S)
            (cauchyApproximationSequenceEncodeBHist R)
            (cauchyApproximationSequenceEncodeBHist E)
            (cauchyApproximationSequenceEncodeBHist H)
            (cauchyApproximationSequenceEncodeBHist C)
            (cauchyApproximationSequenceEncodeBHist P)
            (cauchyApproximationSequenceEncodeBHist N)) =
          some (CauchyApproximationSequenceUp.mk Q D S R E H C P N)
      unfold cauchyApproximationSequenceDecodePacket
      rw [CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode Q,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode D,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode S,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode R,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode E,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode H,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode C,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode P,
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode N]

private theorem CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyApproximationSequenceUp} :
    cauchyApproximationSequenceToEventFlow x =
        cauchyApproximationSequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyApproximationSequenceFromEventFlow (cauchyApproximationSequenceToEventFlow x) =
        cauchyApproximationSequenceFromEventFlow (cauchyApproximationSequenceToEventFlow y) :=
    congrArg cauchyApproximationSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyApproximationSequenceBHistCarrier :
    BHistCarrier CauchyApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyApproximationSequenceToEventFlow
  fromEventFlow := cauchyApproximationSequenceFromEventFlow

instance cauchyApproximationSequenceChapterTasteGate :
    ChapterTasteGate CauchyApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyApproximationSequenceFromEventFlow
        (cauchyApproximationSequenceToEventFlow x) = some x
    exact CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyApproximationSequenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyApproximationSequenceDecodeBHist
        (cauchyApproximationSequenceEncodeBHist h) = h) ∧
      (∀ x : CauchyApproximationSequenceUp,
        cauchyApproximationSequenceFromEventFlow
          (cauchyApproximationSequenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyApproximationSequenceUp,
        cauchyApproximationSequenceToEventFlow x =
          cauchyApproximationSequenceToEventFlow y → x = y) ∧
      cauchyApproximationSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_decode,
      CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyApproximationSequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyApproximationSequenceUp
