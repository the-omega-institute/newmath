import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusRefinementUp : Type where
  | mk (m0 m1 u v t w q e h c p n : BHist) : CauchyModulusRefinementUp
  deriving DecidableEq

def cauchyModulusRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusRefinementEncodeBHist h

def cauchyModulusRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusRefinementDecodeBHist tail)

private theorem cauchyModulusRefinementDecode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyModulusRefinementFields : CauchyModulusRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusRefinementUp.mk m0 m1 u v t w q e h c p n =>
      [m0, m1, u, v, t, w, q, e, h, c, p, n]

def cauchyModulusRefinementToEventFlow : CauchyModulusRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusRefinementFields x).map cauchyModulusRefinementEncodeBHist

private def cauchyModulusRefinementEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusRefinementEventAt index rest

def cauchyModulusRefinementFromEventFlow :
    EventFlow → Option CauchyModulusRefinementUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyModulusRefinementUp.mk
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 0 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 1 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 2 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 3 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 4 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 5 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 6 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 7 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 8 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 9 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 10 ef))
          (cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEventAt 11 ef)))

private theorem cauchyModulusRefinement_round_trip
    (x : CauchyModulusRefinementUp) :
    cauchyModulusRefinementFromEventFlow (cauchyModulusRefinementToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk m0 m1 u v t w q e h c p n =>
      change
        some
          (CauchyModulusRefinementUp.mk
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist m0))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist m1))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist u))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist v))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist t))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist w))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist q))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist e))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist h))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist c))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist p))
            (cauchyModulusRefinementDecodeBHist
              (cauchyModulusRefinementEncodeBHist n))) =
          some (CauchyModulusRefinementUp.mk m0 m1 u v t w q e h c p n)
      rw [cauchyModulusRefinementDecode_encode_bhist m0,
        cauchyModulusRefinementDecode_encode_bhist m1,
        cauchyModulusRefinementDecode_encode_bhist u,
        cauchyModulusRefinementDecode_encode_bhist v,
        cauchyModulusRefinementDecode_encode_bhist t,
        cauchyModulusRefinementDecode_encode_bhist w,
        cauchyModulusRefinementDecode_encode_bhist q,
        cauchyModulusRefinementDecode_encode_bhist e,
        cauchyModulusRefinementDecode_encode_bhist h,
        cauchyModulusRefinementDecode_encode_bhist c,
        cauchyModulusRefinementDecode_encode_bhist p,
        cauchyModulusRefinementDecode_encode_bhist n]

private theorem cauchyModulusRefinementToEventFlow_injective
    {x y : CauchyModulusRefinementUp} :
    cauchyModulusRefinementToEventFlow x = cauchyModulusRefinementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusRefinementFromEventFlow (cauchyModulusRefinementToEventFlow x) =
        cauchyModulusRefinementFromEventFlow (cauchyModulusRefinementToEventFlow y) :=
    congrArg cauchyModulusRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusRefinement_round_trip x).symm
      (Eq.trans hread (cauchyModulusRefinement_round_trip y)))

private theorem cauchyModulusRefinement_field_faithful :
    ∀ x y : CauchyModulusRefinementUp,
      cauchyModulusRefinementFields x = cauchyModulusRefinementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk m0₁ m1₁ u₁ v₁ t₁ w₁ q₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk m0₂ m1₂ u₂ v₂ t₂ w₂ q₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance cauchyModulusRefinementBHistCarrier : BHistCarrier CauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusRefinementToEventFlow
  fromEventFlow := cauchyModulusRefinementFromEventFlow

instance cauchyModulusRefinementChapterTasteGate :
    ChapterTasteGate CauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusRefinementFromEventFlow (cauchyModulusRefinementToEventFlow x) =
        some x
    exact cauchyModulusRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusRefinementToEventFlow_injective heq)

instance cauchyModulusRefinementFieldFaithful :
    FieldFaithful CauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusRefinementFields
  field_faithful := cauchyModulusRefinement_field_faithful

instance cauchyModulusRefinementNontrivial : Nontrivial CauchyModulusRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyModulusRefinementUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyModulusRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusRefinementChapterTasteGate

theorem CauchyModulusRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusRefinementDecodeBHist (cauchyModulusRefinementEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusRefinementUp,
        cauchyModulusRefinementFromEventFlow (cauchyModulusRefinementToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyModulusRefinementUp,
          cauchyModulusRefinementToEventFlow x =
            cauchyModulusRefinementToEventFlow y → x = y) ∧
          cauchyModulusRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨cauchyModulusRefinementDecode_encode_bhist,
      cauchyModulusRefinement_round_trip,
      (fun _ _ heq => cauchyModulusRefinementToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyModulusRefinementUp
