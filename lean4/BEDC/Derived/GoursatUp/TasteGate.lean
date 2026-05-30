import BEDC.Derived.GoursatUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GoursatUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GoursatUp : Type where
  | mk (T H E S M I C P N : BHist) : GoursatUp

def goursatEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: goursatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: goursatEncodeBHist h

def goursatDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (goursatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (goursatDecodeBHist tail)

private theorem GoursatTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, goursatDecodeBHist (goursatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def goursatFields : GoursatUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GoursatUp.mk T H E S M I C P N => [T, H, E, S, M, I, C, P, N]

def goursatToEventFlow : GoursatUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (goursatFields x).map goursatEncodeBHist

private def goursatRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => goursatRawAt n rest

private def goursatLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => goursatLengthEq n rest

def goursatFromEventFlow : EventFlow → Option GoursatUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match goursatLengthEq 9 flow with
      | true =>
          some
            (GoursatUp.mk
              (goursatDecodeBHist (goursatRawAt 0 flow))
              (goursatDecodeBHist (goursatRawAt 1 flow))
              (goursatDecodeBHist (goursatRawAt 2 flow))
              (goursatDecodeBHist (goursatRawAt 3 flow))
              (goursatDecodeBHist (goursatRawAt 4 flow))
              (goursatDecodeBHist (goursatRawAt 5 flow))
              (goursatDecodeBHist (goursatRawAt 6 flow))
              (goursatDecodeBHist (goursatRawAt 7 flow))
              (goursatDecodeBHist (goursatRawAt 8 flow)))
      | false => none

private theorem GoursatTasteGate_single_carrier_alignment_mk_congr
    {T T' H H' E E' S S' M M' I I' C C' P P' N N' : BHist}
    (hT : T' = T) (hH : H' = H) (hE : E' = E) (hS : S' = S)
    (hM : M' = M) (hI : I' = I) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    GoursatUp.mk T' H' E' S' M' I' C' P' N' =
      GoursatUp.mk T H E S M I C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hH
  cases hE
  cases hS
  cases hM
  cases hI
  cases hC
  cases hP
  cases hN
  rfl

private theorem GoursatTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GoursatUp, goursatFromEventFlow (goursatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T H E S M I C P N =>
      change
        some
          (GoursatUp.mk
            (goursatDecodeBHist (goursatEncodeBHist T))
            (goursatDecodeBHist (goursatEncodeBHist H))
            (goursatDecodeBHist (goursatEncodeBHist E))
            (goursatDecodeBHist (goursatEncodeBHist S))
            (goursatDecodeBHist (goursatEncodeBHist M))
            (goursatDecodeBHist (goursatEncodeBHist I))
            (goursatDecodeBHist (goursatEncodeBHist C))
            (goursatDecodeBHist (goursatEncodeBHist P))
            (goursatDecodeBHist (goursatEncodeBHist N))) =
          some (GoursatUp.mk T H E S M I C P N)
      rw [GoursatTasteGate_single_carrier_alignment_decode_encode T,
        GoursatTasteGate_single_carrier_alignment_decode_encode H,
        GoursatTasteGate_single_carrier_alignment_decode_encode E,
        GoursatTasteGate_single_carrier_alignment_decode_encode S,
        GoursatTasteGate_single_carrier_alignment_decode_encode M,
        GoursatTasteGate_single_carrier_alignment_decode_encode I,
        GoursatTasteGate_single_carrier_alignment_decode_encode C,
        GoursatTasteGate_single_carrier_alignment_decode_encode P,
        GoursatTasteGate_single_carrier_alignment_decode_encode N]

private theorem GoursatTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GoursatUp} :
    goursatToEventFlow x = goursatToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      goursatFromEventFlow (goursatToEventFlow x) =
        goursatFromEventFlow (goursatToEventFlow y) :=
    congrArg goursatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GoursatTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GoursatTasteGate_single_carrier_alignment_round_trip y)))

private theorem GoursatTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : GoursatUp, goursatFields x = goursatFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T H E S M I C P N =>
      cases y with
      | mk T' H' E' S' M' I' C' P' N' =>
          cases hfields
          rfl

instance goursatBHistCarrier : BHistCarrier GoursatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := goursatToEventFlow
  fromEventFlow := goursatFromEventFlow

instance goursatChapterTasteGate : ChapterTasteGate GoursatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change goursatFromEventFlow (goursatToEventFlow x) = some x
    exact GoursatTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GoursatTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance goursatFieldFaithful : FieldFaithful GoursatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := goursatFields
  field_faithful := GoursatTasteGate_single_carrier_alignment_fields_faithful

instance goursatNontrivial : BEDC.Meta.TasteGate.Nontrivial GoursatUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GoursatUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GoursatUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GoursatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  goursatChapterTasteGate

theorem GoursatTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GoursatUp) ∧
      Nonempty (FieldFaithful GoursatUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial GoursatUp) ∧
      (∀ h : BHist, goursatDecodeBHist (goursatEncodeBHist h) = h) ∧
      (∀ x : GoursatUp, goursatFromEventFlow (goursatToEventFlow x) = some x) ∧
      (∀ x y : GoursatUp, goursatToEventFlow x = goursatToEventFlow y → x = y) ∧
      goursatEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨goursatChapterTasteGate⟩
  constructor
  · exact ⟨goursatFieldFaithful⟩
  constructor
  · exact ⟨goursatNontrivial⟩
  constructor
  · exact GoursatTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact GoursatTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact GoursatTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.GoursatUp
