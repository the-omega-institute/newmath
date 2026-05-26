import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlgebraicRealUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlgebraicRealUp : Type where
  | mk (P S I D W R E H C K N : BHist) : AlgebraicRealUp

def algebraicRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: algebraicRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: algebraicRealEncodeBHist h

def algebraicRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (algebraicRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (algebraicRealDecodeBHist tail)

private theorem AlgebraicRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, algebraicRealDecodeBHist (algebraicRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def algebraicRealFields : AlgebraicRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlgebraicRealUp.mk P S I D W R E H C K N => [P, S, I, D, W, R, E, H, C, K, N]

def algebraicRealToEventFlow : AlgebraicRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (algebraicRealFields x).map algebraicRealEncodeBHist

private def algebraicRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => algebraicRealRawAt n rest

private def algebraicRealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => algebraicRealLengthEq n rest

def algebraicRealFromEventFlow : EventFlow → Option AlgebraicRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match algebraicRealLengthEq 11 flow with
      | true =>
          some
            (AlgebraicRealUp.mk
              (algebraicRealDecodeBHist (algebraicRealRawAt 0 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 1 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 2 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 3 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 4 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 5 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 6 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 7 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 8 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 9 flow))
              (algebraicRealDecodeBHist (algebraicRealRawAt 10 flow)))
      | false => none

private theorem AlgebraicRealTasteGate_single_carrier_alignment_mk_congr
    {P P' S S' I I' D D' W W' R R' E E' H H' C C' K K' N N' : BHist}
    (hP : P' = P) (hS : S' = S) (hI : I' = I) (hD : D' = D)
    (hW : W' = W) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hK : K' = K) (hN : N' = N) :
    AlgebraicRealUp.mk P' S' I' D' W' R' E' H' C' K' N' =
      AlgebraicRealUp.mk P S I D W R E H C K N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hP
  cases hS
  cases hI
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hK
  cases hN
  rfl

private theorem AlgebraicRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AlgebraicRealUp,
      algebraicRealFromEventFlow (algebraicRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P S I D W R E H C K N =>
      change
        some
          (AlgebraicRealUp.mk
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist P))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist S))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist I))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist D))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist W))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist R))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist E))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist H))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist C))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist K))
            (algebraicRealDecodeBHist (algebraicRealEncodeBHist N))) =
          some (AlgebraicRealUp.mk P S I D W R E H C K N)
      rw [AlgebraicRealTasteGate_single_carrier_alignment_decode_encode P,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode S,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode I,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode D,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode W,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode R,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode E,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode H,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode C,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode K,
        AlgebraicRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem AlgebraicRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlgebraicRealUp} :
    algebraicRealToEventFlow x = algebraicRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      algebraicRealFromEventFlow (algebraicRealToEventFlow x) =
        algebraicRealFromEventFlow (algebraicRealToEventFlow y) :=
    congrArg algebraicRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AlgebraicRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AlgebraicRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem AlgebraicRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AlgebraicRealUp, algebraicRealFields x = algebraicRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P S I D W R E H C K N =>
      cases y with
      | mk P' S' I' D' W' R' E' H' C' K' N' =>
          cases hfields
          rfl

instance algebraicRealBHistCarrier : BHistCarrier AlgebraicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := algebraicRealToEventFlow
  fromEventFlow := algebraicRealFromEventFlow

instance algebraicRealChapterTasteGate : ChapterTasteGate AlgebraicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change algebraicRealFromEventFlow (algebraicRealToEventFlow x) = some x
    exact AlgebraicRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AlgebraicRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance algebraicRealFieldFaithful : FieldFaithful AlgebraicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := algebraicRealFields
  field_faithful := AlgebraicRealTasteGate_single_carrier_alignment_fields_faithful

instance algebraicRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial AlgebraicRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AlgebraicRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AlgebraicRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AlgebraicRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  algebraicRealChapterTasteGate

theorem AlgebraicRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AlgebraicRealUp) ∧
      Nonempty (FieldFaithful AlgebraicRealUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial AlgebraicRealUp) ∧
      (∀ h : BHist, algebraicRealDecodeBHist (algebraicRealEncodeBHist h) = h) ∧
      (∀ x : AlgebraicRealUp,
        algebraicRealFromEventFlow (algebraicRealToEventFlow x) = some x) ∧
      (∀ x y : AlgebraicRealUp,
        algebraicRealToEventFlow x = algebraicRealToEventFlow y → x = y) ∧
      algebraicRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨algebraicRealChapterTasteGate⟩
  constructor
  · exact ⟨algebraicRealFieldFaithful⟩
  constructor
  · exact ⟨algebraicRealNontrivial⟩
  constructor
  · exact AlgebraicRealTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact AlgebraicRealTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact AlgebraicRealTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.AlgebraicRealUp
