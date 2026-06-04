import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ThomaeFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ThomaeFunctionUp : Type where
  | mk (Q D S R E H C P N : BHist) : ThomaeFunctionUp
  deriving DecidableEq

def thomaeFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: thomaeFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: thomaeFunctionEncodeBHist h

def thomaeFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (thomaeFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (thomaeFunctionDecodeBHist tail)

private theorem thomaeFunctionDecode_encode_bhist :
    ∀ h : BHist, thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def thomaeFunctionToEventFlow : ThomaeFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ThomaeFunctionUp.mk Q D S R E H C P N =>
      [[BMark.b0],
        thomaeFunctionEncodeBHist Q,
        [BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        thomaeFunctionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        thomaeFunctionEncodeBHist N]

private def thomaeFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => thomaeFunctionEventAtDefault index rest

def thomaeFunctionFromEventFlow (ef : EventFlow) : Option ThomaeFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ThomaeFunctionUp.mk
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 1 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 3 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 5 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 7 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 9 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 11 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 13 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 15 ef))
      (thomaeFunctionDecodeBHist (thomaeFunctionEventAtDefault 17 ef)))

private theorem thomaeFunction_round_trip :
    ∀ x : ThomaeFunctionUp,
      thomaeFunctionFromEventFlow (thomaeFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S R E H C P N =>
      change
        some
          (ThomaeFunctionUp.mk
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist Q))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist D))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist S))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist R))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist E))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist H))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist C))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist P))
            (thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist N))) =
          some (ThomaeFunctionUp.mk Q D S R E H C P N)
      rw [thomaeFunctionDecode_encode_bhist Q, thomaeFunctionDecode_encode_bhist D,
        thomaeFunctionDecode_encode_bhist S, thomaeFunctionDecode_encode_bhist R,
        thomaeFunctionDecode_encode_bhist E, thomaeFunctionDecode_encode_bhist H,
        thomaeFunctionDecode_encode_bhist C, thomaeFunctionDecode_encode_bhist P,
        thomaeFunctionDecode_encode_bhist N]

private theorem thomaeFunctionToEventFlow_injective {x y : ThomaeFunctionUp} :
    thomaeFunctionToEventFlow x = thomaeFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      thomaeFunctionFromEventFlow (thomaeFunctionToEventFlow x) =
        thomaeFunctionFromEventFlow (thomaeFunctionToEventFlow y) :=
    congrArg thomaeFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (thomaeFunction_round_trip x).symm
      (Eq.trans hread (thomaeFunction_round_trip y)))

instance thomaeFunctionBHistCarrier : BHistCarrier ThomaeFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := thomaeFunctionToEventFlow
  fromEventFlow := thomaeFunctionFromEventFlow

instance thomaeFunctionChapterTasteGate : ChapterTasteGate ThomaeFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change thomaeFunctionFromEventFlow (thomaeFunctionToEventFlow x) = some x
    exact thomaeFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (thomaeFunctionToEventFlow_injective heq)

instance thomaeFunctionFieldFaithful : FieldFaithful ThomaeFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ThomaeFunctionUp.mk Q D S R E H C P N => [Q, D, S, R, E, H, C, P, N]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk Q₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk Q₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hQ rest₁
            injection rest₁ with hD rest₂
            injection rest₂ with hS rest₃
            injection rest₃ with hR rest₄
            injection rest₄ with hE rest₅
            injection rest₅ with hH rest₆
            injection rest₆ with hC rest₇
            injection rest₇ with hP rest₈
            injection rest₈ with hN _
            cases hQ
            cases hD
            cases hS
            cases hR
            cases hE
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance thomaeFunctionNontrivial : Nontrivial ThomaeFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ThomaeFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ThomaeFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hQ _ _ _ _ _ _ _ _
        cases hQ⟩

theorem ThomaeFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, thomaeFunctionDecodeBHist (thomaeFunctionEncodeBHist h) = h) ∧
      (∀ x : ThomaeFunctionUp,
        thomaeFunctionFromEventFlow (thomaeFunctionToEventFlow x) = some x) ∧
        (∀ x y : ThomaeFunctionUp,
          thomaeFunctionToEventFlow x = thomaeFunctionToEventFlow y → x = y) ∧
          thomaeFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact thomaeFunctionDecode_encode_bhist
  · constructor
    · exact thomaeFunction_round_trip
    · constructor
      · intro x y heq
        exact thomaeFunctionToEventFlow_injective heq
      · rfl

end BEDC.Derived.ThomaeFunctionUp
