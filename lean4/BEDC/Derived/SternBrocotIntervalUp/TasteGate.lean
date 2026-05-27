import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotIntervalUp : Type where
  | mk (L R W F S M D Q E H C P N : BHist) : SternBrocotIntervalUp
  deriving DecidableEq

def sternBrocotIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotIntervalEncodeBHist h

def sternBrocotIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotIntervalDecodeBHist tail)

private theorem sternBrocotInterval_decode_encode :
    ∀ h : BHist,
      sternBrocotIntervalDecodeBHist (sternBrocotIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotIntervalFields : SternBrocotIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotIntervalUp.mk L R W F S M D Q E H C P N =>
      [L, R, W, F, S, M, D, Q, E, H, C, P, N]

def sternBrocotIntervalToEventFlow : SternBrocotIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sternBrocotIntervalFields x).map sternBrocotIntervalEncodeBHist

private def sternBrocotIntervalDecodePacket
    (L R W F S M D Q E H C P N : RawEvent) : SternBrocotIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SternBrocotIntervalUp.mk
    (sternBrocotIntervalDecodeBHist L)
    (sternBrocotIntervalDecodeBHist R)
    (sternBrocotIntervalDecodeBHist W)
    (sternBrocotIntervalDecodeBHist F)
    (sternBrocotIntervalDecodeBHist S)
    (sternBrocotIntervalDecodeBHist M)
    (sternBrocotIntervalDecodeBHist D)
    (sternBrocotIntervalDecodeBHist Q)
    (sternBrocotIntervalDecodeBHist E)
    (sternBrocotIntervalDecodeBHist H)
    (sternBrocotIntervalDecodeBHist C)
    (sternBrocotIntervalDecodeBHist P)
    (sternBrocotIntervalDecodeBHist N)

private def sternBrocotIntervalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => sternBrocotIntervalRawAt n rest

private def sternBrocotIntervalLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => sternBrocotIntervalLengthEq n rest

def sternBrocotIntervalFromEventFlow (flow : EventFlow) :
    Option SternBrocotIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match sternBrocotIntervalLengthEq 13 flow with
  | true =>
      some
        (sternBrocotIntervalDecodePacket
          (sternBrocotIntervalRawAt 0 flow)
          (sternBrocotIntervalRawAt 1 flow)
          (sternBrocotIntervalRawAt 2 flow)
          (sternBrocotIntervalRawAt 3 flow)
          (sternBrocotIntervalRawAt 4 flow)
          (sternBrocotIntervalRawAt 5 flow)
          (sternBrocotIntervalRawAt 6 flow)
          (sternBrocotIntervalRawAt 7 flow)
          (sternBrocotIntervalRawAt 8 flow)
          (sternBrocotIntervalRawAt 9 flow)
          (sternBrocotIntervalRawAt 10 flow)
          (sternBrocotIntervalRawAt 11 flow)
          (sternBrocotIntervalRawAt 12 flow))
  | false => none

private theorem sternBrocotInterval_round_trip :
    ∀ x : SternBrocotIntervalUp,
      sternBrocotIntervalFromEventFlow
        (sternBrocotIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W F S M D Q E H C P N =>
      change
        some
          (sternBrocotIntervalDecodePacket
            (sternBrocotIntervalEncodeBHist L)
            (sternBrocotIntervalEncodeBHist R)
            (sternBrocotIntervalEncodeBHist W)
            (sternBrocotIntervalEncodeBHist F)
            (sternBrocotIntervalEncodeBHist S)
            (sternBrocotIntervalEncodeBHist M)
            (sternBrocotIntervalEncodeBHist D)
            (sternBrocotIntervalEncodeBHist Q)
            (sternBrocotIntervalEncodeBHist E)
            (sternBrocotIntervalEncodeBHist H)
            (sternBrocotIntervalEncodeBHist C)
            (sternBrocotIntervalEncodeBHist P)
            (sternBrocotIntervalEncodeBHist N)) =
          some (SternBrocotIntervalUp.mk L R W F S M D Q E H C P N)
      unfold sternBrocotIntervalDecodePacket
      rw [sternBrocotInterval_decode_encode L,
        sternBrocotInterval_decode_encode R,
        sternBrocotInterval_decode_encode W,
        sternBrocotInterval_decode_encode F,
        sternBrocotInterval_decode_encode S,
        sternBrocotInterval_decode_encode M,
        sternBrocotInterval_decode_encode D,
        sternBrocotInterval_decode_encode Q,
        sternBrocotInterval_decode_encode E,
        sternBrocotInterval_decode_encode H,
        sternBrocotInterval_decode_encode C,
        sternBrocotInterval_decode_encode P,
        sternBrocotInterval_decode_encode N]

private theorem sternBrocotIntervalToEventFlow_injective
    {x y : SternBrocotIntervalUp} :
    sternBrocotIntervalToEventFlow x = sternBrocotIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotIntervalFromEventFlow (sternBrocotIntervalToEventFlow x) =
        sternBrocotIntervalFromEventFlow (sternBrocotIntervalToEventFlow y) :=
    congrArg sternBrocotIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sternBrocotInterval_round_trip x).symm
      (Eq.trans hread (sternBrocotInterval_round_trip y)))

instance sternBrocotIntervalBHistCarrier :
    BHistCarrier SternBrocotIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotIntervalToEventFlow
  fromEventFlow := sternBrocotIntervalFromEventFlow

instance sternBrocotIntervalChapterTasteGate :
    ChapterTasteGate SternBrocotIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sternBrocotIntervalFromEventFlow (sternBrocotIntervalToEventFlow x) = some x
    exact sternBrocotInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sternBrocotIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SternBrocotIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sternBrocotIntervalChapterTasteGate

theorem SternBrocotIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sternBrocotIntervalDecodeBHist (sternBrocotIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SternBrocotIntervalUp) ∧
        Nonempty (ChapterTasteGate SternBrocotIntervalUp) ∧
          sternBrocotIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨sternBrocotInterval_decode_encode,
      ⟨sternBrocotIntervalBHistCarrier⟩,
      ⟨sternBrocotIntervalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SternBrocotIntervalUp
