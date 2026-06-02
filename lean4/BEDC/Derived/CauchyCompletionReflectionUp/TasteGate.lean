import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (U V Q F S D A E H C P N : BHist) -> CauchyCompletionReflectionUp
  deriving DecidableEq

def cauchyCompletionReflectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectionEncodeBHist h

def cauchyCompletionReflectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectionDecodeBHist tail)

private theorem cauchyCompletionReflection_decode_encode :
    ∀ h : BHist,
      cauchyCompletionReflectionDecodeBHist
        (cauchyCompletionReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionReflectionFields : CauchyCompletionReflectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectionUp.mk U V Q F S D A E H C P N =>
      [U, V, Q, F, S, D, A, E, H, C, P, N]

def cauchyCompletionReflectionToEventFlow : CauchyCompletionReflectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => cauchyCompletionReflectionFields x |>.map cauchyCompletionReflectionEncodeBHist

private def cauchyCompletionReflectionReadN
    (U V Q F S D A E H C P : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | N :: tail =>
      match tail with
      | [] =>
          some
            (CauchyCompletionReflectionUp.mk
              (cauchyCompletionReflectionDecodeBHist U)
              (cauchyCompletionReflectionDecodeBHist V)
              (cauchyCompletionReflectionDecodeBHist Q)
              (cauchyCompletionReflectionDecodeBHist F)
              (cauchyCompletionReflectionDecodeBHist S)
              (cauchyCompletionReflectionDecodeBHist D)
              (cauchyCompletionReflectionDecodeBHist A)
              (cauchyCompletionReflectionDecodeBHist E)
              (cauchyCompletionReflectionDecodeBHist H)
              (cauchyCompletionReflectionDecodeBHist C)
              (cauchyCompletionReflectionDecodeBHist P)
              (cauchyCompletionReflectionDecodeBHist N))
      | _ :: _ => none
  | [] => none

private def cauchyCompletionReflectionReadP
    (U V Q F S D A E H C : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | P :: tail => cauchyCompletionReflectionReadN U V Q F S D A E H C P tail
  | [] => none

private def cauchyCompletionReflectionReadC
    (U V Q F S D A E H : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | C :: tail => cauchyCompletionReflectionReadP U V Q F S D A E H C tail
  | [] => none

private def cauchyCompletionReflectionReadH
    (U V Q F S D A E : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | H :: tail => cauchyCompletionReflectionReadC U V Q F S D A E H tail
  | [] => none

private def cauchyCompletionReflectionReadE
    (U V Q F S D A : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | E :: tail => cauchyCompletionReflectionReadH U V Q F S D A E tail
  | [] => none

private def cauchyCompletionReflectionReadA
    (U V Q F S D : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | A :: tail => cauchyCompletionReflectionReadE U V Q F S D A tail
  | [] => none

private def cauchyCompletionReflectionReadD
    (U V Q F S : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | D :: tail => cauchyCompletionReflectionReadA U V Q F S D tail
  | [] => none

private def cauchyCompletionReflectionReadS
    (U V Q F : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | S :: tail => cauchyCompletionReflectionReadD U V Q F S tail
  | [] => none

private def cauchyCompletionReflectionReadF
    (U V Q : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | F :: tail => cauchyCompletionReflectionReadS U V Q F tail
  | [] => none

private def cauchyCompletionReflectionReadQ
    (U V : RawEvent) (flow : EventFlow) :
    Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | Q :: tail => cauchyCompletionReflectionReadF U V Q tail
  | [] => none

private def cauchyCompletionReflectionReadV
    (U : RawEvent) (flow : EventFlow) : Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | V :: tail => cauchyCompletionReflectionReadQ U V tail
  | [] => none

def cauchyCompletionReflectionFromEventFlow
    (flow : EventFlow) : Option CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | U :: tail => cauchyCompletionReflectionReadV U tail
  | [] => none

private theorem cauchyCompletionReflection_round_trip
    (x : CauchyCompletionReflectionUp) :
    cauchyCompletionReflectionFromEventFlow
      (cauchyCompletionReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U V Q F S D A E H C P N =>
      change
        some
          (CauchyCompletionReflectionUp.mk
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist U))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist V))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist Q))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist F))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist S))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist D))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist A))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist E))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist H))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist C))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist P))
            (cauchyCompletionReflectionDecodeBHist
              (cauchyCompletionReflectionEncodeBHist N))) =
          some (CauchyCompletionReflectionUp.mk U V Q F S D A E H C P N)
      rw [cauchyCompletionReflection_decode_encode U,
        cauchyCompletionReflection_decode_encode V,
        cauchyCompletionReflection_decode_encode Q,
        cauchyCompletionReflection_decode_encode F,
        cauchyCompletionReflection_decode_encode S,
        cauchyCompletionReflection_decode_encode D,
        cauchyCompletionReflection_decode_encode A,
        cauchyCompletionReflection_decode_encode E,
        cauchyCompletionReflection_decode_encode H,
        cauchyCompletionReflection_decode_encode C,
        cauchyCompletionReflection_decode_encode P,
        cauchyCompletionReflection_decode_encode N]

private theorem cauchyCompletionReflectionToEventFlow_injective
    {x y : CauchyCompletionReflectionUp} :
    cauchyCompletionReflectionToEventFlow x = cauchyCompletionReflectionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectionFromEventFlow (cauchyCompletionReflectionToEventFlow x) =
        cauchyCompletionReflectionFromEventFlow (cauchyCompletionReflectionToEventFlow y) :=
    congrArg cauchyCompletionReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionReflection_round_trip x).symm
      (Eq.trans hread (cauchyCompletionReflection_round_trip y)))

private theorem cauchyCompletionReflectionFields_faithful
    (x y : CauchyCompletionReflectionUp) :
    cauchyCompletionReflectionFields x = cauchyCompletionReflectionFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk U₁ V₁ Q₁ F₁ S₁ D₁ A₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ V₂ Q₂ F₂ S₂ D₂ A₂ E₂ H₂ C₂ P₂ N₂ =>
          injection h with hU hRest₁
          injection hRest₁ with hV hRest₂
          injection hRest₂ with hQ hRest₃
          injection hRest₃ with hF hRest₄
          injection hRest₄ with hS hRest₅
          injection hRest₅ with hD hRest₆
          injection hRest₆ with hA hRest₇
          injection hRest₇ with hE hRest₈
          injection hRest₈ with hH hRest₉
          injection hRest₉ with hC hRest₁₀
          injection hRest₁₀ with hP hRest₁₁
          injection hRest₁₁ with hN _
          subst hU
          subst hV
          subst hQ
          subst hF
          subst hS
          subst hD
          subst hA
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyCompletionReflectionBHistCarrier :
    BHistCarrier CauchyCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectionToEventFlow
  fromEventFlow := cauchyCompletionReflectionFromEventFlow

instance cauchyCompletionReflectionChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectionFromEventFlow
        (cauchyCompletionReflectionToEventFlow x) = some x
    exact cauchyCompletionReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionReflectionToEventFlow_injective heq)

instance cauchyCompletionReflectionFieldFaithful :
    FieldFaithful CauchyCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionReflectionFields
  field_faithful := cauchyCompletionReflectionFields_faithful

instance cauchyCompletionReflectionNontrivial :
    Nontrivial CauchyCompletionReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyCompletionReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectionChapterTasteGate

theorem CauchyCompletionReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectionDecodeBHist
        (cauchyCompletionReflectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionReflectionUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionReflectionUp) ∧
          cauchyCompletionReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyCompletionReflection_decode_encode,
      Nonempty.intro cauchyCompletionReflectionBHistCarrier,
      Nonempty.intro cauchyCompletionReflectionChapterTasteGate,
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectionUp
