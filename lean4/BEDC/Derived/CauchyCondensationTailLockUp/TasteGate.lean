import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationTailLockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationTailLockUp : Type where
  | mk (s w b l t r e h c p n : BHist) : CauchyCondensationTailLockUp
  deriving DecidableEq

def cauchyCondensationTailLockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationTailLockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationTailLockEncodeBHist h

def cauchyCondensationTailLockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationTailLockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationTailLockDecodeBHist tail)

private theorem cauchyCondensationTailLockDecode_encode :
    ∀ h : BHist,
      cauchyCondensationTailLockDecodeBHist
        (cauchyCondensationTailLockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCondensationTailLockFields :
    CauchyCondensationTailLockUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationTailLockUp.mk s w b l t r e h c p n =>
      [s, w, b, l, t, r, e, h, c, p, n]

def cauchyCondensationTailLockToEventFlow :
    CauchyCondensationTailLockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCondensationTailLockFields x).map
        cauchyCondensationTailLockEncodeBHist

private def cauchyCondensationTailLockEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCondensationTailLockEventAtDefault index rest

def cauchyCondensationTailLockFromEventFlow :
    EventFlow → Option CauchyCondensationTailLockUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyCondensationTailLockUp.mk
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 0 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 1 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 2 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 3 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 4 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 5 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 6 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 7 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 8 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 9 ef))
          (cauchyCondensationTailLockDecodeBHist
            (cauchyCondensationTailLockEventAtDefault 10 ef)))

private theorem cauchyCondensationTailLock_round_trip
    (x : CauchyCondensationTailLockUp) :
    cauchyCondensationTailLockFromEventFlow
      (cauchyCondensationTailLockToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk s w b l t r e h c p n =>
      change
        some
          (CauchyCondensationTailLockUp.mk
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist s))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist w))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist b))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist l))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist t))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist r))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist e))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist h))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist c))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist p))
            (cauchyCondensationTailLockDecodeBHist
              (cauchyCondensationTailLockEncodeBHist n))) =
          some (CauchyCondensationTailLockUp.mk s w b l t r e h c p n)
      rw [cauchyCondensationTailLockDecode_encode s,
        cauchyCondensationTailLockDecode_encode w,
        cauchyCondensationTailLockDecode_encode b,
        cauchyCondensationTailLockDecode_encode l,
        cauchyCondensationTailLockDecode_encode t,
        cauchyCondensationTailLockDecode_encode r,
        cauchyCondensationTailLockDecode_encode e,
        cauchyCondensationTailLockDecode_encode h,
        cauchyCondensationTailLockDecode_encode c,
        cauchyCondensationTailLockDecode_encode p,
        cauchyCondensationTailLockDecode_encode n]

private theorem cauchyCondensationTailLockToEventFlow_injective
    {x y : CauchyCondensationTailLockUp} :
    cauchyCondensationTailLockToEventFlow x =
      cauchyCondensationTailLockToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationTailLockFromEventFlow
          (cauchyCondensationTailLockToEventFlow x) =
        cauchyCondensationTailLockFromEventFlow
          (cauchyCondensationTailLockToEventFlow y) :=
    congrArg cauchyCondensationTailLockFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCondensationTailLock_round_trip x).symm
      (Eq.trans hread (cauchyCondensationTailLock_round_trip y)))

private theorem cauchyCondensationTailLock_fields_faithful :
    ∀ x y : CauchyCondensationTailLockUp,
      cauchyCondensationTailLockFields x =
        cauchyCondensationTailLockFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s₁ w₁ b₁ l₁ t₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk s₂ w₂ b₂ l₂ t₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hs tail0
          injection tail0 with hw tail1
          injection tail1 with hb tail2
          injection tail2 with hl tail3
          injection tail3 with ht tail4
          injection tail4 with hr tail5
          injection tail5 with he tail6
          injection tail6 with hh tail7
          injection tail7 with hc tail8
          injection tail8 with hp tail9
          injection tail9 with hn _
          subst hs
          subst hw
          subst hb
          subst hl
          subst ht
          subst hr
          subst he
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance cauchyCondensationTailLockBHistCarrier :
    BHistCarrier CauchyCondensationTailLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationTailLockToEventFlow
  fromEventFlow := cauchyCondensationTailLockFromEventFlow

instance cauchyCondensationTailLockChapterTasteGate :
    ChapterTasteGate CauchyCondensationTailLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCondensationTailLockFromEventFlow
        (cauchyCondensationTailLockToEventFlow x) = some x
    exact cauchyCondensationTailLock_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCondensationTailLockToEventFlow_injective heq)

instance cauchyCondensationTailLockFieldFaithful :
    FieldFaithful CauchyCondensationTailLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCondensationTailLockFields
  field_faithful := cauchyCondensationTailLock_fields_faithful

instance cauchyCondensationTailLockNontrivial :
    Nontrivial CauchyCondensationTailLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCondensationTailLockUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyCondensationTailLockUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCondensationTailLockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCondensationTailLockChapterTasteGate

theorem CauchyCondensationTailLockTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyCondensationTailLockUp) ∧
      Nonempty (ChapterTasteGate CauchyCondensationTailLockUp) ∧
        Nonempty (FieldFaithful CauchyCondensationTailLockUp) ∧
          Nonempty (Nontrivial CauchyCondensationTailLockUp) ∧
            cauchyCondensationTailLockDecodeBHist [BMark.b0] =
              BHist.e0 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cauchyCondensationTailLockBHistCarrier⟩,
      ⟨⟨cauchyCondensationTailLockChapterTasteGate⟩,
        ⟨⟨cauchyCondensationTailLockFieldFaithful⟩,
          ⟨⟨cauchyCondensationTailLockNontrivial⟩, rfl⟩⟩⟩⟩

end BEDC.Derived.CauchyCondensationTailLockUp
