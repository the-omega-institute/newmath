import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalCauchyCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalCauchyCompletionUp : Type where
  | mk :
      (ratSource dyadicTolerance streamWindow regSeqReadback modulus realSeal transport replay
        provenance localName : BHist) →
        RationalCauchyCompletionUp
  deriving DecidableEq

def rationalCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalCauchyCompletionEncodeBHist h

def rationalCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalCauchyCompletionDecodeBHist tail)

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalCauchyCompletionToEventFlow : RationalCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RationalCauchyCompletionUp.mk ratSource dyadicTolerance streamWindow regSeqReadback modulus
      realSeal transport replay provenance localName =>
      [rationalCauchyCompletionEncodeBHist ratSource,
        rationalCauchyCompletionEncodeBHist dyadicTolerance,
        rationalCauchyCompletionEncodeBHist streamWindow,
        rationalCauchyCompletionEncodeBHist regSeqReadback,
        rationalCauchyCompletionEncodeBHist modulus,
        rationalCauchyCompletionEncodeBHist realSeal,
        rationalCauchyCompletionEncodeBHist transport,
        rationalCauchyCompletionEncodeBHist replay,
        rationalCauchyCompletionEncodeBHist provenance,
        rationalCauchyCompletionEncodeBHist localName]

def rationalCauchyCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _ => event
  | Nat.succ n, [] => rationalCauchyCompletionEventAtDefault n []
  | Nat.succ n, _ :: tail => rationalCauchyCompletionEventAtDefault n tail

def rationalCauchyCompletionFromEventFlow :
    EventFlow → Option RationalCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RationalCauchyCompletionUp.mk
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 0 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 1 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 2 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 3 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 4 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 5 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 6 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 7 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 8 ef))
          (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAtDefault 9 ef)))

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip
    (x : RationalCauchyCompletionUp) :
    rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk ratSource dyadicTolerance streamWindow regSeqReadback modulus realSeal transport replay
      provenance localName =>
      change
        some
          (RationalCauchyCompletionUp.mk
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist ratSource))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist dyadicTolerance))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist streamWindow))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist regSeqReadback))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist modulus))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist realSeal))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist transport))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist replay))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist provenance))
            (rationalCauchyCompletionDecodeBHist
              (rationalCauchyCompletionEncodeBHist localName))) =
          some
            (RationalCauchyCompletionUp.mk ratSource dyadicTolerance streamWindow
              regSeqReadback modulus realSeal transport replay provenance localName)
      rw [RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode ratSource,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode streamWindow,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode regSeqReadback,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode modulus,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode realSeal,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode transport,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode replay,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode provenance,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalCauchyCompletionUp} :
    rationalCauchyCompletionToEventFlow x = rationalCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
        rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow y) :=
    congrArg rationalCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip y)))

def rationalCauchyCompletionCarrier :
    BHistCarrier RationalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalCauchyCompletionToEventFlow
  fromEventFlow := rationalCauchyCompletionFromEventFlow

instance rationalCauchyCompletionBHistCarrier :
    BHistCarrier RationalCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalCauchyCompletionCarrier

def rationalCauchyCompletionGate :
    @ChapterTasteGate RationalCauchyCompletionUp rationalCauchyCompletionCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
      some x
    exact RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalCauchyCompletionChapterTasteGate :
    ChapterTasteGate RationalCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalCauchyCompletionGate

theorem RationalCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RationalCauchyCompletionUp) ∧
        Nonempty (ChapterTasteGate RationalCauchyCompletionUp) ∧
          rationalCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨rationalCauchyCompletionCarrier⟩
    · constructor
      · exact
          (⟨rationalCauchyCompletionGate⟩ :
            Nonempty
              (@ChapterTasteGate RationalCauchyCompletionUp rationalCauchyCompletionCarrier))
      · rfl

end BEDC.Derived.RationalCauchyCompletionUp.TasteGate
