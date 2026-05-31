import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyBoundedClosureUp : Type where
  | mk (source metric closureWindow streamWindow readback realSeal transport replay provenance
      nameCert : BHist) : TotallyBoundedClosureUp
  deriving DecidableEq

def totallyBoundedClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedClosureEncodeBHist h

def totallyBoundedClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedClosureDecodeBHist tail)

private theorem TotallyBoundedClosureTasteGate_decode_encode :
    ∀ h : BHist, totallyBoundedClosureDecodeBHist
      (totallyBoundedClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totallyBoundedClosureFields : TotallyBoundedClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedClosureUp.mk source metric closureWindow streamWindow readback
      realSeal transport replay provenance nameCert =>
      [source, metric, closureWindow, streamWindow, readback, realSeal, transport, replay,
        provenance, nameCert]

def totallyBoundedClosureToEventFlow : TotallyBoundedClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (totallyBoundedClosureFields x).map totallyBoundedClosureEncodeBHist

def totallyBoundedClosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totallyBoundedClosureEventAt index rest

def totallyBoundedClosureFromEventFlow (flow : EventFlow) :
    Option TotallyBoundedClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TotallyBoundedClosureUp.mk
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 0 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 1 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 2 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 3 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 4 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 5 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 6 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 7 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 8 flow))
      (totallyBoundedClosureDecodeBHist (totallyBoundedClosureEventAt 9 flow)))

private theorem TotallyBoundedClosureTasteGate_round_trip :
    ∀ x : TotallyBoundedClosureUp,
      totallyBoundedClosureFromEventFlow (totallyBoundedClosureToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source metric closureWindow streamWindow readback realSeal transport replay provenance nameCert =>
      change
        some
          (TotallyBoundedClosureUp.mk
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist source))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist metric))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist closureWindow))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist streamWindow))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist readback))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist realSeal))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist transport))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist replay))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist provenance))
            (totallyBoundedClosureDecodeBHist
              (totallyBoundedClosureEncodeBHist nameCert))) =
          some
            (TotallyBoundedClosureUp.mk source metric closureWindow streamWindow readback
              realSeal transport replay provenance nameCert)
      rw [TotallyBoundedClosureTasteGate_decode_encode source,
        TotallyBoundedClosureTasteGate_decode_encode metric,
        TotallyBoundedClosureTasteGate_decode_encode closureWindow,
        TotallyBoundedClosureTasteGate_decode_encode streamWindow,
        TotallyBoundedClosureTasteGate_decode_encode readback,
        TotallyBoundedClosureTasteGate_decode_encode realSeal,
        TotallyBoundedClosureTasteGate_decode_encode transport,
        TotallyBoundedClosureTasteGate_decode_encode replay,
        TotallyBoundedClosureTasteGate_decode_encode provenance,
        TotallyBoundedClosureTasteGate_decode_encode nameCert]

private theorem totallyBoundedClosureToEventFlow_injective
    {x y : TotallyBoundedClosureUp} :
    totallyBoundedClosureToEventFlow x = totallyBoundedClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedClosureFromEventFlow (totallyBoundedClosureToEventFlow x) =
        totallyBoundedClosureFromEventFlow (totallyBoundedClosureToEventFlow y) :=
    congrArg totallyBoundedClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TotallyBoundedClosureTasteGate_round_trip x).symm
      (Eq.trans hread (TotallyBoundedClosureTasteGate_round_trip y)))

instance totallyBoundedClosureBHistCarrier : BHistCarrier TotallyBoundedClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedClosureToEventFlow
  fromEventFlow := totallyBoundedClosureFromEventFlow

instance totallyBoundedClosureChapterTasteGate :
    ChapterTasteGate TotallyBoundedClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totallyBoundedClosureFromEventFlow (totallyBoundedClosureToEventFlow x) = some x
    exact TotallyBoundedClosureTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totallyBoundedClosureToEventFlow_injective heq)

theorem TotallyBoundedClosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate TotallyBoundedClosureUp) ∧
      (∀ h : BHist, totallyBoundedClosureDecodeBHist
        (totallyBoundedClosureEncodeBHist h) = h) ∧
        (∀ x : TotallyBoundedClosureUp,
          totallyBoundedClosureFromEventFlow (totallyBoundedClosureToEventFlow x) =
            some x) ∧
          (∀ x y : TotallyBoundedClosureUp,
            totallyBoundedClosureToEventFlow x = totallyBoundedClosureToEventFlow y →
              x = y) ∧
            totallyBoundedClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨totallyBoundedClosureChapterTasteGate⟩,
      TotallyBoundedClosureTasteGate_decode_encode,
      TotallyBoundedClosureTasteGate_round_trip,
      fun _ _ heq => totallyBoundedClosureToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.TotallyBoundedClosureUp
