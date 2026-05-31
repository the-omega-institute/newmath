import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalizationUp : Type where
  | mk (family selector streamWindow tolerance readback realSeal transport replay provenance
      nameCert : BHist) : RegularCauchyDiagonalizationUp
  deriving DecidableEq

def regularCauchyDiagonalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalizationEncodeBHist h

def regularCauchyDiagonalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalizationDecodeBHist tail)

private theorem RegularCauchyDiagonalizationTasteGate_decode_encode :
    ∀ h : BHist,
      regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalizationFields : RegularCauchyDiagonalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalizationUp.mk family selector streamWindow tolerance readback
      realSeal transport replay provenance nameCert =>
      [family, selector, streamWindow, tolerance, readback, realSeal, transport, replay,
        provenance, nameCert]

def regularCauchyDiagonalizationToEventFlow : RegularCauchyDiagonalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyDiagonalizationFields x).map regularCauchyDiagonalizationEncodeBHist

def regularCauchyDiagonalizationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalizationEventAt index rest

def regularCauchyDiagonalizationFromEventFlow
    (flow : EventFlow) : Option RegularCauchyDiagonalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDiagonalizationUp.mk
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 0 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 1 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 2 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 3 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 4 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 5 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 6 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 7 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 8 flow))
      (regularCauchyDiagonalizationDecodeBHist
        (regularCauchyDiagonalizationEventAt 9 flow)))

private theorem RegularCauchyDiagonalizationTasteGate_round_trip :
    ∀ x : RegularCauchyDiagonalizationUp,
      regularCauchyDiagonalizationFromEventFlow
        (regularCauchyDiagonalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family selector streamWindow tolerance readback realSeal transport replay provenance nameCert =>
      change
        some
          (RegularCauchyDiagonalizationUp.mk
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist family))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist selector))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist streamWindow))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist tolerance))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist readback))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist realSeal))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist transport))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist replay))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist provenance))
            (regularCauchyDiagonalizationDecodeBHist
              (regularCauchyDiagonalizationEncodeBHist nameCert))) =
          some
            (RegularCauchyDiagonalizationUp.mk family selector streamWindow tolerance readback
              realSeal transport replay provenance nameCert)
      rw [RegularCauchyDiagonalizationTasteGate_decode_encode family,
        RegularCauchyDiagonalizationTasteGate_decode_encode selector,
        RegularCauchyDiagonalizationTasteGate_decode_encode streamWindow,
        RegularCauchyDiagonalizationTasteGate_decode_encode tolerance,
        RegularCauchyDiagonalizationTasteGate_decode_encode readback,
        RegularCauchyDiagonalizationTasteGate_decode_encode realSeal,
        RegularCauchyDiagonalizationTasteGate_decode_encode transport,
        RegularCauchyDiagonalizationTasteGate_decode_encode replay,
        RegularCauchyDiagonalizationTasteGate_decode_encode provenance,
        RegularCauchyDiagonalizationTasteGate_decode_encode nameCert]

private theorem regularCauchyDiagonalizationToEventFlow_injective
    {x y : RegularCauchyDiagonalizationUp} :
    regularCauchyDiagonalizationToEventFlow x =
      regularCauchyDiagonalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalizationFromEventFlow
          (regularCauchyDiagonalizationToEventFlow x) =
        regularCauchyDiagonalizationFromEventFlow
          (regularCauchyDiagonalizationToEventFlow y) :=
    congrArg regularCauchyDiagonalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyDiagonalizationTasteGate_round_trip x).symm
      (Eq.trans hread (RegularCauchyDiagonalizationTasteGate_round_trip y)))

instance regularCauchyDiagonalizationBHistCarrier :
    BHistCarrier RegularCauchyDiagonalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalizationToEventFlow
  fromEventFlow := regularCauchyDiagonalizationFromEventFlow

instance regularCauchyDiagonalizationChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalizationFromEventFlow
        (regularCauchyDiagonalizationToEventFlow x) = some x
    exact RegularCauchyDiagonalizationTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalizationToEventFlow_injective heq)

theorem RegularCauchyDiagonalizationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyDiagonalizationUp) ∧
      (∀ h : BHist,
        regularCauchyDiagonalizationDecodeBHist
          (regularCauchyDiagonalizationEncodeBHist h) = h) ∧
        (∀ x : RegularCauchyDiagonalizationUp,
          regularCauchyDiagonalizationFromEventFlow
            (regularCauchyDiagonalizationToEventFlow x) = some x) ∧
          (∀ x y : RegularCauchyDiagonalizationUp,
            regularCauchyDiagonalizationToEventFlow x =
              regularCauchyDiagonalizationToEventFlow y → x = y) ∧
            regularCauchyDiagonalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularCauchyDiagonalizationChapterTasteGate⟩,
      RegularCauchyDiagonalizationTasteGate_decode_encode,
      RegularCauchyDiagonalizationTasteGate_round_trip,
      fun _ _ heq => regularCauchyDiagonalizationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyDiagonalizationUp
