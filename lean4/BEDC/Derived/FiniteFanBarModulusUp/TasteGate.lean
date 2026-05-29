import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteFanBarModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteFanBarModulusUp : Type where
  | mk (B K L Q R U H C P N : BHist) : FiniteFanBarModulusUp
  deriving DecidableEq

def finiteFanBarModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteFanBarModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteFanBarModulusEncodeBHist h

def finiteFanBarModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteFanBarModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteFanBarModulusDecodeBHist tail)

private theorem finiteFanBarModulus_decode_encode_bhist :
    ∀ h : BHist, finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteFanBarModulusFields : FiniteFanBarModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteFanBarModulusUp.mk B K L Q R U H C P N => [B, K, L, Q, R, U, H, C, P, N]

def finiteFanBarModulusToEventFlow : FiniteFanBarModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteFanBarModulusFields x).map finiteFanBarModulusEncodeBHist

private def finiteFanBarModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteFanBarModulusEventAtDefault index rest

def finiteFanBarModulusFromEventFlow (ef : EventFlow) : Option FiniteFanBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteFanBarModulusUp.mk
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 0 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 1 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 2 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 3 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 4 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 5 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 6 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 7 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 8 ef))
      (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEventAtDefault 9 ef)))

private theorem finiteFanBarModulus_round_trip :
    ∀ x : FiniteFanBarModulusUp,
      finiteFanBarModulusFromEventFlow
        (finiteFanBarModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B K L Q R U H C P N =>
      change
        some
          (FiniteFanBarModulusUp.mk
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist B))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist K))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist L))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist Q))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist R))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist U))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist H))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist C))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist P))
            (finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist N))) =
          some (FiniteFanBarModulusUp.mk B K L Q R U H C P N)
      rw [finiteFanBarModulus_decode_encode_bhist B,
        finiteFanBarModulus_decode_encode_bhist K,
        finiteFanBarModulus_decode_encode_bhist L,
        finiteFanBarModulus_decode_encode_bhist Q,
        finiteFanBarModulus_decode_encode_bhist R,
        finiteFanBarModulus_decode_encode_bhist U,
        finiteFanBarModulus_decode_encode_bhist H,
        finiteFanBarModulus_decode_encode_bhist C,
        finiteFanBarModulus_decode_encode_bhist P,
        finiteFanBarModulus_decode_encode_bhist N]

private theorem finiteFanBarModulusToEventFlow_injective {x y : FiniteFanBarModulusUp} :
    finiteFanBarModulusToEventFlow x =
      finiteFanBarModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteFanBarModulusFromEventFlow
          (finiteFanBarModulusToEventFlow x) =
        finiteFanBarModulusFromEventFlow
          (finiteFanBarModulusToEventFlow y) :=
    congrArg finiteFanBarModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteFanBarModulus_round_trip x).symm
      (Eq.trans hread (finiteFanBarModulus_round_trip y)))

private theorem finiteFanBarModulus_field_faithful :
    ∀ x y : FiniteFanBarModulusUp,
      finiteFanBarModulusFields x = finiteFanBarModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B K L Q R U H C P N =>
      cases y with
      | mk B' K' L' Q' R' U' H' C' P' N' =>
          cases hfields
          rfl

instance finiteFanBarModulusBHistCarrier : BHistCarrier FiniteFanBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteFanBarModulusToEventFlow
  fromEventFlow := finiteFanBarModulusFromEventFlow

instance finiteFanBarModulusChapterTasteGate : ChapterTasteGate FiniteFanBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteFanBarModulusFromEventFlow (finiteFanBarModulusToEventFlow x) = some x
    exact finiteFanBarModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteFanBarModulusToEventFlow_injective heq)

instance finiteFanBarModulusFieldFaithful : FieldFaithful FiniteFanBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteFanBarModulusFields
  field_faithful := finiteFanBarModulus_field_faithful

instance finiteFanBarModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteFanBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteFanBarModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteFanBarModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteFanBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteFanBarModulusChapterTasteGate

theorem FiniteFanBarModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteFanBarModulusUp) ∧
      Nonempty (FieldFaithful FiniteFanBarModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteFanBarModulusUp) ∧
      (∀ h : BHist, finiteFanBarModulusDecodeBHist (finiteFanBarModulusEncodeBHist h) = h) ∧
      (∀ x : FiniteFanBarModulusUp,
        finiteFanBarModulusFromEventFlow (finiteFanBarModulusToEventFlow x) = some x) ∧
      (∀ x y : FiniteFanBarModulusUp,
        finiteFanBarModulusToEventFlow x = finiteFanBarModulusToEventFlow y → x = y) ∧
      finiteFanBarModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨finiteFanBarModulusChapterTasteGate⟩,
      ⟨finiteFanBarModulusFieldFaithful⟩,
      ⟨finiteFanBarModulusNontrivial⟩,
      finiteFanBarModulus_decode_encode_bhist,
      finiteFanBarModulus_round_trip,
      (fun _ _ heq => finiteFanBarModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteFanBarModulusUp
