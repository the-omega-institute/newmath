import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalCauchyGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalCauchyGapUp : Type where
  | mk (Q D W R E H C P N : BHist) : RationalCauchyGapUp
  deriving DecidableEq

def rationalCauchyGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalCauchyGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalCauchyGapEncodeBHist h

def rationalCauchyGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalCauchyGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalCauchyGapDecodeBHist tail)

private theorem RationalCauchyGapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalCauchyGapFields : RationalCauchyGapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalCauchyGapUp.mk Q D W R E H C P N => [Q, D, W, R, E, H, C, P, N]

def rationalCauchyGapToEventFlow : RationalCauchyGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalCauchyGapFields x).map rationalCauchyGapEncodeBHist

private def rationalCauchyGapRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => rationalCauchyGapRawAt n rest

private def rationalCauchyGapLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => rationalCauchyGapLengthEq n rest

def rationalCauchyGapFromEventFlow : EventFlow → Option RationalCauchyGapUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match rationalCauchyGapLengthEq 9 flow with
      | true =>
          some
            (RationalCauchyGapUp.mk
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 0 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 1 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 2 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 3 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 4 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 5 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 6 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 7 flow))
              (rationalCauchyGapDecodeBHist (rationalCauchyGapRawAt 8 flow)))
      | false => none

private theorem rationalCauchyGap_round_trip :
    ∀ x : RationalCauchyGapUp,
      rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D W R E H C P N =>
      change
        some
          (RationalCauchyGapUp.mk
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist Q))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist D))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist W))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist R))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist E))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist H))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist C))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist P))
            (rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist N))) =
          some (RationalCauchyGapUp.mk Q D W R E H C P N)
      rw [RationalCauchyGapTasteGate_single_carrier_alignment_decode Q,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode D,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode W,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode R,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode E,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode H,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode C,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode P,
        RationalCauchyGapTasteGate_single_carrier_alignment_decode N]

private theorem rationalCauchyGapToEventFlow_injective {x y : RationalCauchyGapUp} :
    rationalCauchyGapToEventFlow x = rationalCauchyGapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) =
        rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow y) :=
    congrArg rationalCauchyGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalCauchyGap_round_trip x).symm
      (Eq.trans hread (rationalCauchyGap_round_trip y)))

private theorem rationalCauchyGap_field_faithful :
    ∀ x y : RationalCauchyGapUp,
      rationalCauchyGapFields x = rationalCauchyGapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance rationalCauchyGapBHistCarrier : BHistCarrier RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalCauchyGapToEventFlow
  fromEventFlow := rationalCauchyGapFromEventFlow

instance rationalCauchyGapChapterTasteGate : ChapterTasteGate RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x
    exact rationalCauchyGap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalCauchyGapToEventFlow_injective heq)

instance rationalCauchyGapFieldFaithful : FieldFaithful RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalCauchyGapFields
  field_faithful := rationalCauchyGap_field_faithful

instance rationalCauchyGapNontrivial : Nontrivial RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalCauchyGapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalCauchyGapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RationalCauchyGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalCauchyGapChapterTasteGate

theorem RationalCauchyGapTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RationalCauchyGapUp) ∧
      Nonempty (FieldFaithful RationalCauchyGapUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RationalCauchyGapUp) ∧
      (∀ h : BHist, rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist h) = h) ∧
      (∀ x : RationalCauchyGapUp,
        rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x) ∧
      (∀ x y : RationalCauchyGapUp,
        rationalCauchyGapToEventFlow x = rationalCauchyGapToEventFlow y → x = y) ∧
      rationalCauchyGapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro rationalCauchyGapChapterTasteGate,
      Nonempty.intro rationalCauchyGapFieldFaithful,
      Nonempty.intro rationalCauchyGapNontrivial,
      RationalCauchyGapTasteGate_single_carrier_alignment_decode,
      rationalCauchyGap_round_trip,
      (fun _ _ heq => rationalCauchyGapToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RationalCauchyGapUp
