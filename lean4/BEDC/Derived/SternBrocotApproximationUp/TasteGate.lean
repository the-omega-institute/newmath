import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotApproximationUp : Type where
  | mk (L U M T W R E H C P N : BHist) : SternBrocotApproximationUp
  deriving DecidableEq

def sternBrocotApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotApproximationEncodeBHist h

def sternBrocotApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotApproximationDecodeBHist tail)

private theorem sternBrocotApproximation_decode_encode :
    ∀ h : BHist,
      sternBrocotApproximationDecodeBHist
        (sternBrocotApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotApproximationFields : SternBrocotApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotApproximationUp.mk L U M T W R E H C P N =>
      [L, U, M, T, W, R, E, H, C, P, N]

def sternBrocotApproximationToEventFlow : SternBrocotApproximationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sternBrocotApproximationFields x).map sternBrocotApproximationEncodeBHist

private def sternBrocotApproximationDecodePacket
    (L U M T W R E H C P N : RawEvent) : SternBrocotApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SternBrocotApproximationUp.mk
    (sternBrocotApproximationDecodeBHist L)
    (sternBrocotApproximationDecodeBHist U)
    (sternBrocotApproximationDecodeBHist M)
    (sternBrocotApproximationDecodeBHist T)
    (sternBrocotApproximationDecodeBHist W)
    (sternBrocotApproximationDecodeBHist R)
    (sternBrocotApproximationDecodeBHist E)
    (sternBrocotApproximationDecodeBHist H)
    (sternBrocotApproximationDecodeBHist C)
    (sternBrocotApproximationDecodeBHist P)
    (sternBrocotApproximationDecodeBHist N)

private def sternBrocotApproximationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => sternBrocotApproximationRawAt n rest

private def sternBrocotApproximationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => sternBrocotApproximationLengthEq n rest

def sternBrocotApproximationFromEventFlow (flow : EventFlow) :
    Option SternBrocotApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match sternBrocotApproximationLengthEq 11 flow with
  | true =>
      some
        (sternBrocotApproximationDecodePacket
          (sternBrocotApproximationRawAt 0 flow)
          (sternBrocotApproximationRawAt 1 flow)
          (sternBrocotApproximationRawAt 2 flow)
          (sternBrocotApproximationRawAt 3 flow)
          (sternBrocotApproximationRawAt 4 flow)
          (sternBrocotApproximationRawAt 5 flow)
          (sternBrocotApproximationRawAt 6 flow)
          (sternBrocotApproximationRawAt 7 flow)
          (sternBrocotApproximationRawAt 8 flow)
          (sternBrocotApproximationRawAt 9 flow)
          (sternBrocotApproximationRawAt 10 flow))
  | false => none

private theorem sternBrocotApproximation_round_trip :
    ∀ x : SternBrocotApproximationUp,
      sternBrocotApproximationFromEventFlow
        (sternBrocotApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U M T W R E H C P N =>
      change
        some
          (sternBrocotApproximationDecodePacket
            (sternBrocotApproximationEncodeBHist L)
            (sternBrocotApproximationEncodeBHist U)
            (sternBrocotApproximationEncodeBHist M)
            (sternBrocotApproximationEncodeBHist T)
            (sternBrocotApproximationEncodeBHist W)
            (sternBrocotApproximationEncodeBHist R)
            (sternBrocotApproximationEncodeBHist E)
            (sternBrocotApproximationEncodeBHist H)
            (sternBrocotApproximationEncodeBHist C)
            (sternBrocotApproximationEncodeBHist P)
            (sternBrocotApproximationEncodeBHist N)) =
          some (SternBrocotApproximationUp.mk L U M T W R E H C P N)
      unfold sternBrocotApproximationDecodePacket
      rw [sternBrocotApproximation_decode_encode L,
        sternBrocotApproximation_decode_encode U,
        sternBrocotApproximation_decode_encode M,
        sternBrocotApproximation_decode_encode T,
        sternBrocotApproximation_decode_encode W,
        sternBrocotApproximation_decode_encode R,
        sternBrocotApproximation_decode_encode E,
        sternBrocotApproximation_decode_encode H,
        sternBrocotApproximation_decode_encode C,
        sternBrocotApproximation_decode_encode P,
        sternBrocotApproximation_decode_encode N]

private theorem sternBrocotApproximationToEventFlow_injective
    {x y : SternBrocotApproximationUp} :
    sternBrocotApproximationToEventFlow x = sternBrocotApproximationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotApproximationFromEventFlow (sternBrocotApproximationToEventFlow x) =
        sternBrocotApproximationFromEventFlow (sternBrocotApproximationToEventFlow y) :=
    congrArg sternBrocotApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sternBrocotApproximation_round_trip x).symm
      (Eq.trans hread (sternBrocotApproximation_round_trip y)))

instance sternBrocotApproximationBHistCarrier :
    BHistCarrier SternBrocotApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotApproximationToEventFlow
  fromEventFlow := sternBrocotApproximationFromEventFlow

instance sternBrocotApproximationChapterTasteGate :
    ChapterTasteGate SternBrocotApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sternBrocotApproximationFromEventFlow
        (sternBrocotApproximationToEventFlow x) = some x
    exact sternBrocotApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sternBrocotApproximationToEventFlow_injective heq)

theorem SternBrocotApproximationTasteGate_single_carrier_alignment :
    sternBrocotApproximationFromEventFlow
        (sternBrocotApproximationToEventFlow
          (SternBrocotApproximationUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (SternBrocotApproximationUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ∧
      sternBrocotApproximationToEventFlow
        (SternBrocotApproximationUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        sternBrocotApproximationToEventFlow
          (SternBrocotApproximationUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.SternBrocotApproximationUp
