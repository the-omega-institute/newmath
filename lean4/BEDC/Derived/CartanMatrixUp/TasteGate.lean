import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CartanMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CartanMatrixUp : Type where
  | mk (I A D O S R W C H K P N : BHist) : CartanMatrixUp
  deriving DecidableEq

def cartanMatrixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cartanMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cartanMatrixEncodeBHist h

def cartanMatrixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cartanMatrixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cartanMatrixDecodeBHist tail)

private theorem CartanMatrixTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cartanMatrixDecodeBHist (cartanMatrixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cartanMatrixFields : CartanMatrixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CartanMatrixUp.mk I A D O S R W C H K P N => [I, A, D, O, S, R, W, C, H, K, P, N]

def cartanMatrixToEventFlow : CartanMatrixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cartanMatrixFields x).map cartanMatrixEncodeBHist

private def cartanMatrixEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cartanMatrixEventAt index rest

def cartanMatrixFromEventFlow (ef : EventFlow) : Option CartanMatrixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CartanMatrixUp.mk
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 0 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 1 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 2 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 3 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 4 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 5 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 6 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 7 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 8 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 9 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 10 ef))
      (cartanMatrixDecodeBHist (cartanMatrixEventAt 11 ef)))

private theorem CartanMatrixTasteGate_single_carrier_alignment_round_trip
    (x : CartanMatrixUp) :
    cartanMatrixFromEventFlow (cartanMatrixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I A D O S R W C H K P N =>
      change
        some
          (CartanMatrixUp.mk
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist I))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist A))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist D))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist O))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist S))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist R))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist W))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist C))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist H))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist K))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist P))
            (cartanMatrixDecodeBHist (cartanMatrixEncodeBHist N))) =
          some (CartanMatrixUp.mk I A D O S R W C H K P N)
      rw [CartanMatrixTasteGate_single_carrier_alignment_decode_encode I,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode A,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode D,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode O,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode S,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode R,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode W,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode C,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode H,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode K,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode P,
        CartanMatrixTasteGate_single_carrier_alignment_decode_encode N]

private theorem CartanMatrixTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CartanMatrixUp} :
    cartanMatrixToEventFlow x = cartanMatrixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cartanMatrixFromEventFlow (cartanMatrixToEventFlow x) =
        cartanMatrixFromEventFlow (cartanMatrixToEventFlow y) :=
    congrArg cartanMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CartanMatrixTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CartanMatrixTasteGate_single_carrier_alignment_round_trip y)))

private theorem CartanMatrixTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CartanMatrixUp, cartanMatrixFields x = cartanMatrixFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ A₁ D₁ O₁ S₁ R₁ W₁ C₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk I₂ A₂ D₂ O₂ S₂ R₂ W₂ C₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance cartanMatrixBHistCarrier : BHistCarrier CartanMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cartanMatrixToEventFlow
  fromEventFlow := cartanMatrixFromEventFlow

instance cartanMatrixChapterTasteGate : ChapterTasteGate CartanMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cartanMatrixFromEventFlow (cartanMatrixToEventFlow x) = some x
    exact CartanMatrixTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CartanMatrixTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cartanMatrixFieldFaithful : FieldFaithful CartanMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cartanMatrixFields
  field_faithful := CartanMatrixTasteGate_single_carrier_alignment_fields_faithful

instance cartanMatrixNontrivial : Nontrivial CartanMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CartanMatrixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CartanMatrixUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CartanMatrixTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CartanMatrixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cartanMatrixChapterTasteGate

theorem CartanMatrixTasteGate_single_carrier_alignment :
    (∀ h : BHist, cartanMatrixDecodeBHist (cartanMatrixEncodeBHist h) = h) ∧
      (∀ x : CartanMatrixUp,
        cartanMatrixFromEventFlow (cartanMatrixToEventFlow x) = some x) ∧
        (∀ x y : CartanMatrixUp,
          cartanMatrixToEventFlow x = cartanMatrixToEventFlow y → x = y) ∧
          cartanMatrixEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CartanMatrixTasteGate_single_carrier_alignment_decode_encode,
      CartanMatrixTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CartanMatrixTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CartanMatrixUp
