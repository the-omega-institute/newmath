import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixStreamUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixStreamUp : Type where
  | mk (k W D R H C P N : BHist) : FinitePrefixStreamUp
  deriving DecidableEq

def finitePrefixStreamEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixStreamEncodeBHist h

def finitePrefixStreamDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixStreamDecodeBHist tail)

private theorem finitePrefixStream_decode_encode :
    ∀ h : BHist, finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finitePrefixStreamFields : FinitePrefixStreamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixStreamUp.mk k W D R H C P N => [k, W, D, R, H, C, P, N]

def finitePrefixStreamToEventFlow : FinitePrefixStreamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map finitePrefixStreamEncodeBHist (finitePrefixStreamFields x)

private def finitePrefixStreamRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finitePrefixStreamRawAt index rest

def finitePrefixStreamFromEventFlow (flow : EventFlow) : Option FinitePrefixStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FinitePrefixStreamUp.mk
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 0 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 1 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 2 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 3 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 4 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 5 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 6 flow))
      (finitePrefixStreamDecodeBHist (finitePrefixStreamRawAt 7 flow)))

private theorem finitePrefixStream_round_trip :
    ∀ x : FinitePrefixStreamUp,
      finitePrefixStreamFromEventFlow (finitePrefixStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk k W D R H C P N =>
      change
        some
          (FinitePrefixStreamUp.mk
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist k))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist W))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist D))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist R))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist H))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist C))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist P))
            (finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist N))) =
          some (FinitePrefixStreamUp.mk k W D R H C P N)
      rw [finitePrefixStream_decode_encode k,
        finitePrefixStream_decode_encode W,
        finitePrefixStream_decode_encode D,
        finitePrefixStream_decode_encode R,
        finitePrefixStream_decode_encode H,
        finitePrefixStream_decode_encode C,
        finitePrefixStream_decode_encode P,
        finitePrefixStream_decode_encode N]

theorem finitePrefixStreamToEventFlow_injective {x y : FinitePrefixStreamUp} :
    finitePrefixStreamToEventFlow x = finitePrefixStreamToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixStreamFromEventFlow (finitePrefixStreamToEventFlow x) =
        finitePrefixStreamFromEventFlow (finitePrefixStreamToEventFlow y) :=
    congrArg finitePrefixStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePrefixStream_round_trip x).symm
      (Eq.trans hread (finitePrefixStream_round_trip y)))

instance finitePrefixStreamBHistCarrier : BHistCarrier FinitePrefixStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixStreamToEventFlow
  fromEventFlow := finitePrefixStreamFromEventFlow

instance finitePrefixStreamChapterTasteGate : ChapterTasteGate FinitePrefixStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finitePrefixStreamFromEventFlow (finitePrefixStreamToEventFlow x) = some x
    exact finitePrefixStream_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePrefixStreamToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FinitePrefixStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePrefixStreamChapterTasteGate

theorem FinitePrefixStreamTasteGate_single_carrier_alignment :
    (∀ h : BHist, finitePrefixStreamDecodeBHist (finitePrefixStreamEncodeBHist h) = h) ∧
      (∀ x : FinitePrefixStreamUp,
        finitePrefixStreamFromEventFlow (finitePrefixStreamToEventFlow x) = some x) ∧
        (∀ x y : FinitePrefixStreamUp,
          finitePrefixStreamToEventFlow x = finitePrefixStreamToEventFlow y → x = y) ∧
          finitePrefixStreamEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨finitePrefixStream_decode_encode,
      finitePrefixStream_round_trip,
      fun x y => finitePrefixStreamToEventFlow_injective,
      rfl⟩

end BEDC.Derived.FinitePrefixStreamUp.TasteGate
