import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionWindowFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionWindowFunctorUp : Type where
  | mk (W D R E F H C P N : BHist) : RealCompletionWindowFunctorUp
  deriving DecidableEq

def realCompletionWindowFunctorFields : RealCompletionWindowFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionWindowFunctorUp.mk W D R E F H C P N => [W, D, R, E, F, H, C, P, N]

def realCompletionWindowFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionWindowFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionWindowFunctorEncodeBHist h

def realCompletionWindowFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionWindowFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionWindowFunctorDecodeBHist tail)

private theorem realCompletionWindowFunctor_decode_encode_bhist :
    ∀ h : BHist,
      realCompletionWindowFunctorDecodeBHist (realCompletionWindowFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletionWindowFunctorToEventFlow :
    RealCompletionWindowFunctorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCompletionWindowFunctorFields x).map realCompletionWindowFunctorEncodeBHist

private def realCompletionWindowFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionWindowFunctorEventAtDefault index rest

def realCompletionWindowFunctorFromEventFlow
    (ef : EventFlow) : Option RealCompletionWindowFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionWindowFunctorUp.mk
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 0 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 1 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 2 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 3 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 4 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 5 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 6 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 7 ef))
      (realCompletionWindowFunctorDecodeBHist
        (realCompletionWindowFunctorEventAtDefault 8 ef)))

private theorem realCompletionWindowFunctor_round_trip :
    ∀ x : RealCompletionWindowFunctorUp,
      realCompletionWindowFunctorFromEventFlow
        (realCompletionWindowFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D R E F H C P N =>
      change
        some
          (RealCompletionWindowFunctorUp.mk
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist W))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist D))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist R))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist E))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist F))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist H))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist C))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist P))
            (realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist N))) =
          some (RealCompletionWindowFunctorUp.mk W D R E F H C P N)
      rw [realCompletionWindowFunctor_decode_encode_bhist W,
        realCompletionWindowFunctor_decode_encode_bhist D,
        realCompletionWindowFunctor_decode_encode_bhist R,
        realCompletionWindowFunctor_decode_encode_bhist E,
        realCompletionWindowFunctor_decode_encode_bhist F,
        realCompletionWindowFunctor_decode_encode_bhist H,
        realCompletionWindowFunctor_decode_encode_bhist C,
        realCompletionWindowFunctor_decode_encode_bhist P,
        realCompletionWindowFunctor_decode_encode_bhist N]

private theorem realCompletionWindowFunctorToEventFlow_injective
    {x y : RealCompletionWindowFunctorUp} :
    realCompletionWindowFunctorToEventFlow x =
      realCompletionWindowFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionWindowFunctorFromEventFlow (realCompletionWindowFunctorToEventFlow x) =
        realCompletionWindowFunctorFromEventFlow (realCompletionWindowFunctorToEventFlow y) :=
    congrArg realCompletionWindowFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionWindowFunctor_round_trip x).symm
      (Eq.trans hread (realCompletionWindowFunctor_round_trip y)))

instance realCompletionWindowFunctorBHistCarrier :
    BHistCarrier RealCompletionWindowFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionWindowFunctorToEventFlow
  fromEventFlow := realCompletionWindowFunctorFromEventFlow

instance realCompletionWindowFunctorChapterTasteGate :
    ChapterTasteGate RealCompletionWindowFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionWindowFunctorFromEventFlow
        (realCompletionWindowFunctorToEventFlow x) = some x
    exact realCompletionWindowFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionWindowFunctorToEventFlow_injective heq)

instance realCompletionWindowFunctorFieldFaithful :
    FieldFaithful RealCompletionWindowFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionWindowFunctorFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk W₁ D₁ R₁ E₁ F₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk W₂ D₂ R₂ E₂ F₂ H₂ C₂ P₂ N₂ =>
            injection h with hW rest₁
            injection rest₁ with hD rest₂
            injection rest₂ with hR rest₃
            injection rest₃ with hE rest₄
            injection rest₄ with hF rest₅
            injection rest₅ with hH rest₆
            injection rest₆ with hC rest₇
            injection rest₇ with hP rest₈
            injection rest₈ with hN _
            cases hW
            cases hD
            cases hR
            cases hE
            cases hF
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance realCompletionWindowFunctorNontrivial : Nontrivial RealCompletionWindowFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionWindowFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionWindowFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hW _ _ _ _ _ _ _ _
        cases hW⟩

theorem RealCompletionWindowFunctorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealCompletionWindowFunctorUp) ∧
      Nonempty (FieldFaithful RealCompletionWindowFunctorUp) ∧
        Nonempty (Nontrivial RealCompletionWindowFunctorUp) ∧
          (∀ h : BHist,
            realCompletionWindowFunctorDecodeBHist
              (realCompletionWindowFunctorEncodeBHist h) = h) ∧
            (∀ x : RealCompletionWindowFunctorUp,
              realCompletionWindowFunctorFromEventFlow
                (realCompletionWindowFunctorToEventFlow x) = some x) ∧
              (∀ x y : RealCompletionWindowFunctorUp,
                realCompletionWindowFunctorToEventFlow x =
                  realCompletionWindowFunctorToEventFlow y → x = y) ∧
                realCompletionWindowFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨realCompletionWindowFunctorChapterTasteGate⟩,
      ⟨realCompletionWindowFunctorFieldFaithful⟩,
      ⟨realCompletionWindowFunctorNontrivial⟩,
      realCompletionWindowFunctor_decode_encode_bhist,
      realCompletionWindowFunctor_round_trip,
      (fun _ _ heq => realCompletionWindowFunctorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCompletionWindowFunctorUp
