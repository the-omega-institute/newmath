import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicWindowSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicWindowSealUp : Type where
  | mk (q w r b z s h c p n : BHist) : DyadicWindowSealUp
  deriving DecidableEq

def dyadicWindowSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicWindowSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicWindowSealEncodeBHist h

def dyadicWindowSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicWindowSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicWindowSealDecodeBHist tail)

private theorem dyadicWindowSeal_decode_encode_bhist :
    ∀ h : BHist, dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicWindowSealToEventFlow : DyadicWindowSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicWindowSealUp.mk q w r b z s h c p n =>
      [[BMark.b0],
        dyadicWindowSealEncodeBHist q,
        [BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicWindowSealEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicWindowSealEncodeBHist n]

private def dyadicWindowSealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicWindowSealEventAtDefault index rest

def dyadicWindowSealFromEventFlow (ef : EventFlow) : Option DyadicWindowSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicWindowSealUp.mk
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 1 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 3 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 5 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 7 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 9 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 11 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 13 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 15 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 17 ef))
      (dyadicWindowSealDecodeBHist (dyadicWindowSealEventAtDefault 19 ef)))

private theorem dyadicWindowSeal_round_trip :
    ∀ x : DyadicWindowSealUp,
      dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q w r b z s h c p n =>
      change
        some
          (DyadicWindowSealUp.mk
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist q))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist w))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist r))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist b))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist z))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist s))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist h))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist c))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist p))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist n))) =
          some (DyadicWindowSealUp.mk q w r b z s h c p n)
      rw [dyadicWindowSeal_decode_encode_bhist q, dyadicWindowSeal_decode_encode_bhist w,
        dyadicWindowSeal_decode_encode_bhist r, dyadicWindowSeal_decode_encode_bhist b,
        dyadicWindowSeal_decode_encode_bhist z, dyadicWindowSeal_decode_encode_bhist s,
        dyadicWindowSeal_decode_encode_bhist h, dyadicWindowSeal_decode_encode_bhist c,
        dyadicWindowSeal_decode_encode_bhist p, dyadicWindowSeal_decode_encode_bhist n]

private theorem dyadicWindowSealToEventFlow_injective {x y : DyadicWindowSealUp} :
    dyadicWindowSealToEventFlow x = dyadicWindowSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) =
        dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow y) :=
    congrArg dyadicWindowSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicWindowSeal_round_trip x).symm
      (Eq.trans hread (dyadicWindowSeal_round_trip y)))

private def dyadicWindowSealFields : DyadicWindowSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicWindowSealUp.mk q w r b z s h c p n => [q, w, r, b, z, s, h, c, p, n]

private theorem dyadicWindowSeal_field_faithful :
    ∀ x y : DyadicWindowSealUp, dyadicWindowSealFields x = dyadicWindowSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ w₁ r₁ b₁ z₁ s₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk q₂ w₂ r₂ b₂ z₂ s₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance dyadicWindowSealBHistCarrier : BHistCarrier DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicWindowSealToEventFlow
  fromEventFlow := dyadicWindowSealFromEventFlow

instance dyadicWindowSealChapterTasteGate : ChapterTasteGate DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x
    exact dyadicWindowSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicWindowSealToEventFlow_injective heq)

instance dyadicWindowSealFieldFaithful : FieldFaithful DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicWindowSealFields
  field_faithful := dyadicWindowSeal_field_faithful

instance dyadicWindowSealNontrivial : Nontrivial DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicWindowSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicWindowSealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicWindowSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicWindowSealChapterTasteGate

theorem DyadicWindowSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicWindowSealUp) ∧
      Nonempty (FieldFaithful DyadicWindowSealUp) ∧
        Nonempty (Nontrivial DyadicWindowSealUp) ∧
          (∀ h : BHist, dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist h) = h) ∧
            (∀ x : DyadicWindowSealUp,
              dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x) ∧
              (∀ x y : DyadicWindowSealUp,
                dyadicWindowSealToEventFlow x = dyadicWindowSealToEventFlow y → x = y) ∧
                dyadicWindowSealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨dyadicWindowSealChapterTasteGate⟩,
      ⟨dyadicWindowSealFieldFaithful⟩,
      ⟨dyadicWindowSealNontrivial⟩,
      dyadicWindowSeal_decode_encode_bhist,
      dyadicWindowSeal_round_trip,
      (fun _ _ heq => dyadicWindowSealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicWindowSealUp
