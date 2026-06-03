import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MertensCauchyProductTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MertensCauchyProductTheoremUp : Type where
  | mk (A B W K T Q R E H C P N : BHist) : MertensCauchyProductTheoremUp
  deriving DecidableEq

def mertensCauchyProductTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mertensCauchyProductTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mertensCauchyProductTheoremEncodeBHist h

def mertensCauchyProductTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mertensCauchyProductTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mertensCauchyProductTheoremDecodeBHist tail)

private theorem MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      mertensCauchyProductTheoremDecodeBHist
        (mertensCauchyProductTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mertensCauchyProductTheoremFields :
    MertensCauchyProductTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MertensCauchyProductTheoremUp.mk A B W K T Q R E H C P N =>
      [A, B, W, K, T, Q, R, E, H, C, P, N]

def mertensCauchyProductTheoremToEventFlow :
    MertensCauchyProductTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mertensCauchyProductTheoremFields x).map
      mertensCauchyProductTheoremEncodeBHist

private def mertensCauchyProductTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => mertensCauchyProductTheoremEventAt n rest
  | _, [] => []

private def mertensCauchyProductTheoremLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => mertensCauchyProductTheoremLengthEq n rest

private def mertensCauchyProductTheoremDecodePacket
    (A B W K T Q R E H C P N : RawEvent) :
    MertensCauchyProductTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MertensCauchyProductTheoremUp.mk
    (mertensCauchyProductTheoremDecodeBHist A)
    (mertensCauchyProductTheoremDecodeBHist B)
    (mertensCauchyProductTheoremDecodeBHist W)
    (mertensCauchyProductTheoremDecodeBHist K)
    (mertensCauchyProductTheoremDecodeBHist T)
    (mertensCauchyProductTheoremDecodeBHist Q)
    (mertensCauchyProductTheoremDecodeBHist R)
    (mertensCauchyProductTheoremDecodeBHist E)
    (mertensCauchyProductTheoremDecodeBHist H)
    (mertensCauchyProductTheoremDecodeBHist C)
    (mertensCauchyProductTheoremDecodeBHist P)
    (mertensCauchyProductTheoremDecodeBHist N)

def mertensCauchyProductTheoremFromEventFlow
    (flow : EventFlow) : Option MertensCauchyProductTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match mertensCauchyProductTheoremLengthEq 12 flow with
  | true =>
      some
        (mertensCauchyProductTheoremDecodePacket
          (mertensCauchyProductTheoremEventAt 0 flow)
          (mertensCauchyProductTheoremEventAt 1 flow)
          (mertensCauchyProductTheoremEventAt 2 flow)
          (mertensCauchyProductTheoremEventAt 3 flow)
          (mertensCauchyProductTheoremEventAt 4 flow)
          (mertensCauchyProductTheoremEventAt 5 flow)
          (mertensCauchyProductTheoremEventAt 6 flow)
          (mertensCauchyProductTheoremEventAt 7 flow)
          (mertensCauchyProductTheoremEventAt 8 flow)
          (mertensCauchyProductTheoremEventAt 9 flow)
          (mertensCauchyProductTheoremEventAt 10 flow)
          (mertensCauchyProductTheoremEventAt 11 flow))
  | false => none

private theorem MertensCauchyProductTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MertensCauchyProductTheoremUp,
      mertensCauchyProductTheoremFromEventFlow
        (mertensCauchyProductTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B W K T Q R E H C P N =>
      change
        some
          (mertensCauchyProductTheoremDecodePacket
            (mertensCauchyProductTheoremEncodeBHist A)
            (mertensCauchyProductTheoremEncodeBHist B)
            (mertensCauchyProductTheoremEncodeBHist W)
            (mertensCauchyProductTheoremEncodeBHist K)
            (mertensCauchyProductTheoremEncodeBHist T)
            (mertensCauchyProductTheoremEncodeBHist Q)
            (mertensCauchyProductTheoremEncodeBHist R)
            (mertensCauchyProductTheoremEncodeBHist E)
            (mertensCauchyProductTheoremEncodeBHist H)
            (mertensCauchyProductTheoremEncodeBHist C)
            (mertensCauchyProductTheoremEncodeBHist P)
            (mertensCauchyProductTheoremEncodeBHist N)) =
          some (MertensCauchyProductTheoremUp.mk A B W K T Q R E H C P N)
      unfold mertensCauchyProductTheoremDecodePacket
      rw [MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode A,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode B,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode W,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode K,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode T,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode Q,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode R,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode E,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode H,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode C,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode P,
        MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode N]

private theorem MertensCauchyProductTheoremTasteGate_single_carrier_alignment_injective
    {x y : MertensCauchyProductTheoremUp} :
    mertensCauchyProductTheoremToEventFlow x =
      mertensCauchyProductTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mertensCauchyProductTheoremFromEventFlow
          (mertensCauchyProductTheoremToEventFlow x) =
        mertensCauchyProductTheoremFromEventFlow
          (mertensCauchyProductTheoremToEventFlow y) :=
    congrArg mertensCauchyProductTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MertensCauchyProductTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MertensCauchyProductTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance mertensCauchyProductTheoremBHistCarrier :
    BHistCarrier MertensCauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mertensCauchyProductTheoremToEventFlow
  fromEventFlow := mertensCauchyProductTheoremFromEventFlow

instance mertensCauchyProductTheoremChapterTasteGate :
    ChapterTasteGate MertensCauchyProductTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      mertensCauchyProductTheoremFromEventFlow
        (mertensCauchyProductTheoremToEventFlow x) = some x
    exact MertensCauchyProductTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MertensCauchyProductTheoremTasteGate_single_carrier_alignment_injective heq)

theorem MertensCauchyProductTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      mertensCauchyProductTheoremDecodeBHist
        (mertensCauchyProductTheoremEncodeBHist h) = h) ∧
      (∀ x : MertensCauchyProductTheoremUp,
        mertensCauchyProductTheoremFromEventFlow
          (mertensCauchyProductTheoremToEventFlow x) = some x) ∧
        (∀ x y : MertensCauchyProductTheoremUp,
          mertensCauchyProductTheoremToEventFlow x =
            mertensCauchyProductTheoremToEventFlow y → x = y) ∧
          mertensCauchyProductTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MertensCauchyProductTheoremTasteGate_single_carrier_alignment_decode
  · constructor
    · exact MertensCauchyProductTheoremTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MertensCauchyProductTheoremTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MertensCauchyProductTheoremUp
