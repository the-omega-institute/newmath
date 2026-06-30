import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelSourceChannelLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelSourceChannelLedgerUp : Type where
  | mk (G K A E Q R T M F H C P N : BHist) : KernelSourceChannelLedgerUp
  deriving DecidableEq

def kernelSourceChannelLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelSourceChannelLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelSourceChannelLedgerEncodeBHist h

def kernelSourceChannelLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelSourceChannelLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelSourceChannelLedgerDecodeBHist tail)

private theorem KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kernelSourceChannelLedgerDecodeBHist
      (kernelSourceChannelLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kernelSourceChannelLedgerToEventFlow : KernelSourceChannelLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelSourceChannelLedgerUp.mk G K A E Q R T M F H C P N =>
      [kernelSourceChannelLedgerEncodeBHist G,
        kernelSourceChannelLedgerEncodeBHist K,
        kernelSourceChannelLedgerEncodeBHist A,
        kernelSourceChannelLedgerEncodeBHist E,
        kernelSourceChannelLedgerEncodeBHist Q,
        kernelSourceChannelLedgerEncodeBHist R,
        kernelSourceChannelLedgerEncodeBHist T,
        kernelSourceChannelLedgerEncodeBHist M,
        kernelSourceChannelLedgerEncodeBHist F,
        kernelSourceChannelLedgerEncodeBHist H,
        kernelSourceChannelLedgerEncodeBHist C,
        kernelSourceChannelLedgerEncodeBHist P,
        kernelSourceChannelLedgerEncodeBHist N]

private def kernelSourceChannelLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kernelSourceChannelLedgerEventAtDefault index rest

def kernelSourceChannelLedgerFromEventFlow (ef : EventFlow) :
    Option KernelSourceChannelLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KernelSourceChannelLedgerUp.mk
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 0 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 1 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 2 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 3 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 4 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 5 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 6 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 7 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 8 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 9 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 10 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 11 ef))
      (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEventAtDefault 12 ef)))

private theorem KernelSourceChannelLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KernelSourceChannelLedgerUp,
      kernelSourceChannelLedgerFromEventFlow (kernelSourceChannelLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G K A E Q R T M F H C P N =>
      change
        some
          (KernelSourceChannelLedgerUp.mk
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist G))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist K))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist A))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist E))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist Q))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist R))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist T))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist M))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist F))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist H))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist C))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist P))
            (kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist N))) =
          some (KernelSourceChannelLedgerUp.mk G K A E Q R T M F H C P N)
      rw [KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode G,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode K,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode A,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode E,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode Q,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode R,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode T,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode M,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode F,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode H,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode C,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode P,
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode N]

private theorem KernelSourceChannelLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KernelSourceChannelLedgerUp} :
    kernelSourceChannelLedgerToEventFlow x = kernelSourceChannelLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelSourceChannelLedgerFromEventFlow (kernelSourceChannelLedgerToEventFlow x) =
        kernelSourceChannelLedgerFromEventFlow (kernelSourceChannelLedgerToEventFlow y) :=
    congrArg kernelSourceChannelLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KernelSourceChannelLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KernelSourceChannelLedgerTasteGate_single_carrier_alignment_round_trip y)))

instance kernelSourceChannelLedgerBHistCarrier : BHistCarrier KernelSourceChannelLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelSourceChannelLedgerToEventFlow
  fromEventFlow := kernelSourceChannelLedgerFromEventFlow

instance kernelSourceChannelLedgerChapterTasteGate :
    ChapterTasteGate KernelSourceChannelLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelSourceChannelLedgerFromEventFlow (kernelSourceChannelLedgerToEventFlow x) =
      some x
    exact KernelSourceChannelLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KernelSourceChannelLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate KernelSourceChannelLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelSourceChannelLedgerChapterTasteGate

theorem KernelSourceChannelLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelSourceChannelLedgerDecodeBHist (kernelSourceChannelLedgerEncodeBHist h) = h) ∧
      (∀ x : KernelSourceChannelLedgerUp,
        kernelSourceChannelLedgerFromEventFlow (kernelSourceChannelLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : KernelSourceChannelLedgerUp,
          kernelSourceChannelLedgerToEventFlow x = kernelSourceChannelLedgerToEventFlow y →
            x = y) ∧
          kernelSourceChannelLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KernelSourceChannelLedgerTasteGate_single_carrier_alignment_decode_encode,
      KernelSourceChannelLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KernelSourceChannelLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KernelSourceChannelLedgerUp.TasteGate
