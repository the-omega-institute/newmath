import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedCompletionMonadUp : Type where
  | mk (a m u b w r d l h c p n : BHist) : SeparatedCompletionMonadUp
  deriving DecidableEq

def separatedCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedCompletionMonadEncodeBHist h

def separatedCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedCompletionMonadDecodeBHist tail)

private theorem separatedCompletionMonadDecode_encode :
    ∀ h : BHist,
      separatedCompletionMonadDecodeBHist
        (separatedCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def separatedCompletionMonadFields :
    SeparatedCompletionMonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedCompletionMonadUp.mk a m u b w r d l h c p n =>
      [a, m, u, b, w, r, d, l, h, c, p, n]

def separatedCompletionMonadToEventFlow :
    SeparatedCompletionMonadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (separatedCompletionMonadFields x).map separatedCompletionMonadEncodeBHist

private def separatedCompletionMonadEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      separatedCompletionMonadEventAtDefault index rest

def separatedCompletionMonadFromEventFlow :
    EventFlow → Option SeparatedCompletionMonadUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SeparatedCompletionMonadUp.mk
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 0 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 1 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 2 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 3 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 4 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 5 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 6 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 7 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 8 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 9 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 10 ef))
          (separatedCompletionMonadDecodeBHist
            (separatedCompletionMonadEventAtDefault 11 ef)))

private theorem separatedCompletionMonad_round_trip
    (x : SeparatedCompletionMonadUp) :
    separatedCompletionMonadFromEventFlow
      (separatedCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk a m u b w r d l h c p n =>
      change
        some
          (SeparatedCompletionMonadUp.mk
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist a))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist m))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist u))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist b))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist w))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist r))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist d))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist l))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist h))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist c))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist p))
            (separatedCompletionMonadDecodeBHist
              (separatedCompletionMonadEncodeBHist n))) =
          some (SeparatedCompletionMonadUp.mk a m u b w r d l h c p n)
      rw [separatedCompletionMonadDecode_encode a,
        separatedCompletionMonadDecode_encode m,
        separatedCompletionMonadDecode_encode u,
        separatedCompletionMonadDecode_encode b,
        separatedCompletionMonadDecode_encode w,
        separatedCompletionMonadDecode_encode r,
        separatedCompletionMonadDecode_encode d,
        separatedCompletionMonadDecode_encode l,
        separatedCompletionMonadDecode_encode h,
        separatedCompletionMonadDecode_encode c,
        separatedCompletionMonadDecode_encode p,
        separatedCompletionMonadDecode_encode n]

private theorem separatedCompletionMonadToEventFlow_injective
    {x y : SeparatedCompletionMonadUp} :
    separatedCompletionMonadToEventFlow x =
      separatedCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedCompletionMonadFromEventFlow
          (separatedCompletionMonadToEventFlow x) =
        separatedCompletionMonadFromEventFlow
          (separatedCompletionMonadToEventFlow y) :=
    congrArg separatedCompletionMonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedCompletionMonad_round_trip x).symm
      (Eq.trans hread (separatedCompletionMonad_round_trip y)))

private theorem separatedCompletionMonad_fields_faithful :
    ∀ x y : SeparatedCompletionMonadUp,
      separatedCompletionMonadFields x =
        separatedCompletionMonadFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a₁ m₁ u₁ b₁ w₁ r₁ d₁ l₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk a₂ m₂ u₂ b₂ w₂ r₂ d₂ l₂ h₂ c₂ p₂ n₂ =>
          injection hfields with ha tail0
          injection tail0 with hm tail1
          injection tail1 with hu tail2
          injection tail2 with hb tail3
          injection tail3 with hw tail4
          injection tail4 with hr tail5
          injection tail5 with hd tail6
          injection tail6 with hl tail7
          injection tail7 with hh tail8
          injection tail8 with hc tail9
          injection tail9 with hp tail10
          injection tail10 with hn _
          subst ha
          subst hm
          subst hu
          subst hb
          subst hw
          subst hr
          subst hd
          subst hl
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance separatedCompletionMonadBHistCarrier :
    BHistCarrier SeparatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedCompletionMonadToEventFlow
  fromEventFlow := separatedCompletionMonadFromEventFlow

instance separatedCompletionMonadChapterTasteGate :
    ChapterTasteGate SeparatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedCompletionMonadFromEventFlow
        (separatedCompletionMonadToEventFlow x) = some x
    exact separatedCompletionMonad_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedCompletionMonadToEventFlow_injective heq)

instance separatedCompletionMonadFieldFaithful :
    FieldFaithful SeparatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedCompletionMonadFields
  field_faithful := separatedCompletionMonad_fields_faithful

instance separatedCompletionMonadNontrivial :
    Nontrivial SeparatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedCompletionMonadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SeparatedCompletionMonadUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedCompletionMonadChapterTasteGate

theorem SeparatedCompletionMonadTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SeparatedCompletionMonadUp) ∧
      Nonempty (ChapterTasteGate SeparatedCompletionMonadUp) ∧
        Nonempty (FieldFaithful SeparatedCompletionMonadUp) ∧
          Nonempty (Nontrivial SeparatedCompletionMonadUp) ∧
            separatedCompletionMonadDecodeBHist [BMark.b1] =
              BHist.e1 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨separatedCompletionMonadBHistCarrier⟩,
      ⟨⟨separatedCompletionMonadChapterTasteGate⟩,
        ⟨⟨separatedCompletionMonadFieldFaithful⟩,
          ⟨⟨separatedCompletionMonadNontrivial⟩, rfl⟩⟩⟩⟩

end BEDC.Derived.SeparatedCompletionMonadUp
