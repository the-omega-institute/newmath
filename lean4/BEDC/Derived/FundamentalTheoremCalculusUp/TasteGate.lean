import BEDC.Derived.FundamentalTheoremCalculusUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FundamentalTheoremCalculusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FundamentalTheoremCalculusUp : Type where
  | mk (D I A T Q S G R H C P N : BHist) : FundamentalTheoremCalculusUp
  deriving DecidableEq

def fundamentalTheoremCalculusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fundamentalTheoremCalculusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fundamentalTheoremCalculusEncodeBHist h

def fundamentalTheoremCalculusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fundamentalTheoremCalculusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fundamentalTheoremCalculusDecodeBHist tail)

private theorem fundamentalTheoremCalculus_decode_encode :
    ∀ h : BHist,
      fundamentalTheoremCalculusDecodeBHist
        (fundamentalTheoremCalculusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fundamentalTheoremCalculusFields :
    FundamentalTheoremCalculusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FundamentalTheoremCalculusUp.mk D I A T Q S G R H C P N =>
      [D, I, A, T, Q, S, G, R, H, C, P, N]

def fundamentalTheoremCalculusToEventFlow :
    FundamentalTheoremCalculusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => fundamentalTheoremCalculusFields x |>.map fundamentalTheoremCalculusEncodeBHist

private def fundamentalTheoremCalculusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fundamentalTheoremCalculusRawAt n rest

def fundamentalTheoremCalculusFromEventFlow
    (flow : EventFlow) : Option FundamentalTheoremCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FundamentalTheoremCalculusUp.mk
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 0 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 1 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 2 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 3 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 4 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 5 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 6 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 7 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 8 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 9 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 10 flow))
      (fundamentalTheoremCalculusDecodeBHist (fundamentalTheoremCalculusRawAt 11 flow)))

private theorem fundamentalTheoremCalculus_round_trip
    (x : FundamentalTheoremCalculusUp) :
    fundamentalTheoremCalculusFromEventFlow
        (fundamentalTheoremCalculusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D I A T Q S G R H C P N =>
      change
        some
          (FundamentalTheoremCalculusUp.mk
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist D))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist I))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist A))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist T))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist Q))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist S))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist G))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist R))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist H))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist C))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist P))
            (fundamentalTheoremCalculusDecodeBHist
              (fundamentalTheoremCalculusEncodeBHist N))) =
          some (FundamentalTheoremCalculusUp.mk D I A T Q S G R H C P N)
      rw [fundamentalTheoremCalculus_decode_encode D,
        fundamentalTheoremCalculus_decode_encode I,
        fundamentalTheoremCalculus_decode_encode A,
        fundamentalTheoremCalculus_decode_encode T,
        fundamentalTheoremCalculus_decode_encode Q,
        fundamentalTheoremCalculus_decode_encode S,
        fundamentalTheoremCalculus_decode_encode G,
        fundamentalTheoremCalculus_decode_encode R,
        fundamentalTheoremCalculus_decode_encode H,
        fundamentalTheoremCalculus_decode_encode C,
        fundamentalTheoremCalculus_decode_encode P,
        fundamentalTheoremCalculus_decode_encode N]

private theorem fundamentalTheoremCalculusToEventFlow_injective
    {x y : FundamentalTheoremCalculusUp} :
    fundamentalTheoremCalculusToEventFlow x =
        fundamentalTheoremCalculusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fundamentalTheoremCalculusFromEventFlow
          (fundamentalTheoremCalculusToEventFlow x) =
        fundamentalTheoremCalculusFromEventFlow
          (fundamentalTheoremCalculusToEventFlow y) :=
    congrArg fundamentalTheoremCalculusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fundamentalTheoremCalculus_round_trip x).symm
      (Eq.trans hread (fundamentalTheoremCalculus_round_trip y)))

instance fundamentalTheoremCalculusBHistCarrier :
    BHistCarrier FundamentalTheoremCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fundamentalTheoremCalculusToEventFlow
  fromEventFlow := fundamentalTheoremCalculusFromEventFlow

instance fundamentalTheoremCalculusChapterTasteGate :
    ChapterTasteGate FundamentalTheoremCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fundamentalTheoremCalculusFromEventFlow
          (fundamentalTheoremCalculusToEventFlow x) =
        some x
    exact fundamentalTheoremCalculus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fundamentalTheoremCalculusToEventFlow_injective heq)

theorem FundamentalTheoremCalculusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FundamentalTheoremCalculusUp) ∧
      fundamentalTheoremCalculusEncodeBHist (BHist.e1 BHist.Empty) =
        ([BMark.b1] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨fundamentalTheoremCalculusChapterTasteGate⟩, rfl⟩

end BEDC.Derived.FundamentalTheoremCalculusUp
