import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedOpenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedOpenUp : Type where
  | mk (L R S Q W E T H C P N : BHist) : LocatedOpenUp
  deriving DecidableEq

def locatedOpenEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedOpenEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedOpenEncodeBHist h

def locatedOpenDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedOpenDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedOpenDecodeBHist tail)

private theorem locatedOpenDecode_encode :
    ∀ h : BHist, locatedOpenDecodeBHist (locatedOpenEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedOpenFields : LocatedOpenUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedOpenUp.mk l r s q w e t h c p n => [l, r, s, q, w, e, t, h, c, p, n]

def locatedOpenToEventFlow : LocatedOpenUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedOpenFields x).map locatedOpenEncodeBHist

private def locatedOpenEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedOpenEventAt index rest

def locatedOpenFromEventFlow : EventFlow → Option LocatedOpenUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedOpenUp.mk
        (locatedOpenDecodeBHist (locatedOpenEventAt 0 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 1 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 2 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 3 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 4 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 5 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 6 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 7 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 8 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 9 ef))
        (locatedOpenDecodeBHist (locatedOpenEventAt 10 ef)))

private theorem locatedOpen_round_trip :
    ∀ x : LocatedOpenUp, locatedOpenFromEventFlow (locatedOpenToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk l r s q w e t h c p n =>
      change
        some
            (LocatedOpenUp.mk
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist l))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist r))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist s))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist q))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist w))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist e))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist t))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist h))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist c))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist p))
              (locatedOpenDecodeBHist (locatedOpenEncodeBHist n))) =
          some (LocatedOpenUp.mk l r s q w e t h c p n)
      rw [locatedOpenDecode_encode l, locatedOpenDecode_encode r,
        locatedOpenDecode_encode s, locatedOpenDecode_encode q, locatedOpenDecode_encode w,
        locatedOpenDecode_encode e, locatedOpenDecode_encode t, locatedOpenDecode_encode h,
        locatedOpenDecode_encode c, locatedOpenDecode_encode p, locatedOpenDecode_encode n]

private theorem locatedOpenToEventFlow_injective {x y : LocatedOpenUp} :
    locatedOpenToEventFlow x = locatedOpenToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedOpenFromEventFlow (locatedOpenToEventFlow x) =
        locatedOpenFromEventFlow (locatedOpenToEventFlow y) :=
    congrArg locatedOpenFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedOpen_round_trip x).symm
      (Eq.trans hread (locatedOpen_round_trip y)))

private theorem locatedOpen_fields_faithful :
    ∀ x y : LocatedOpenUp, locatedOpenFields x = locatedOpenFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk l₁ r₁ s₁ q₁ w₁ e₁ t₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk l₂ r₂ s₂ q₂ w₂ e₂ t₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance locatedOpenBHistCarrier : BHistCarrier LocatedOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedOpenToEventFlow
  fromEventFlow := locatedOpenFromEventFlow

instance locatedOpenChapterTasteGate : ChapterTasteGate LocatedOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := locatedOpen_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedOpenToEventFlow_injective heq)

instance locatedOpenFieldFaithful : FieldFaithful LocatedOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedOpenFields
  field_faithful := locatedOpen_fields_faithful

instance locatedOpenNontrivial : Nontrivial LocatedOpenUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedOpenUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedOpenUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

namespace TasteGate

theorem LocatedOpenTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedOpenDecodeBHist (locatedOpenEncodeBHist h) = h) ∧
      (∀ x : LocatedOpenUp, locatedOpenFromEventFlow (locatedOpenToEventFlow x) = some x) ∧
        (∀ x y : LocatedOpenUp, locatedOpenToEventFlow x = locatedOpenToEventFlow y → x = y) ∧
          locatedOpenEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact locatedOpenDecode_encode
  · constructor
    · exact locatedOpen_round_trip
    · constructor
      · intro x y heq
        exact locatedOpenToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.LocatedOpenUp
