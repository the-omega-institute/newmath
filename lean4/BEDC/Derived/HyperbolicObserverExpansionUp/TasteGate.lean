import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicObserverExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicObserverExpansionUp : Type where
  | mk (V B M S R Q F H C P N : BHist) : HyperbolicObserverExpansionUp
  deriving DecidableEq

def hyperbolicObserverExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicObserverExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicObserverExpansionEncodeBHist h

def hyperbolicObserverExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicObserverExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicObserverExpansionDecodeBHist tail)

private theorem HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicObserverExpansionFields :
    HyperbolicObserverExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicObserverExpansionUp.mk V B M S R Q F H C P N =>
      [V, B, M, S, R, Q, F, H, C, P, N]

def hyperbolicObserverExpansionToEventFlow :
    HyperbolicObserverExpansionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (hyperbolicObserverExpansionFields x).map hyperbolicObserverExpansionEncodeBHist

def hyperbolicObserverExpansionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicObserverExpansionEventAt index rest

def hyperbolicObserverExpansionFromEventFlow
    (eventFlow : EventFlow) : Option HyperbolicObserverExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicObserverExpansionUp.mk
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 0 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 1 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 2 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 3 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 4 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 5 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 6 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 7 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 8 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 9 eventFlow))
      (hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEventAt 10 eventFlow)))

private theorem HyperbolicObserverExpansionTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicObserverExpansionUp) :
    hyperbolicObserverExpansionFromEventFlow
        (hyperbolicObserverExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V B M S R Q F H C P N =>
      change
        some
          (HyperbolicObserverExpansionUp.mk
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist V))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist B))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist M))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist S))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist R))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist Q))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist F))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist H))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist C))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist P))
            (hyperbolicObserverExpansionDecodeBHist
              (hyperbolicObserverExpansionEncodeBHist N))) =
          some (HyperbolicObserverExpansionUp.mk V B M S R Q F H C P N)
      rw [HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode V,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode B,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode S,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode R,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode Q,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode F,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicObserverExpansionToEventFlow_injective
    {x y : HyperbolicObserverExpansionUp} :
    hyperbolicObserverExpansionToEventFlow x =
      hyperbolicObserverExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicObserverExpansionFromEventFlow
          (hyperbolicObserverExpansionToEventFlow x) =
        hyperbolicObserverExpansionFromEventFlow
          (hyperbolicObserverExpansionToEventFlow y) :=
    congrArg hyperbolicObserverExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicObserverExpansionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicObserverExpansionTasteGate_single_carrier_alignment_round_trip y)))

instance hyperbolicObserverExpansionBHistCarrier :
    BHistCarrier HyperbolicObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicObserverExpansionToEventFlow
  fromEventFlow := hyperbolicObserverExpansionFromEventFlow

instance hyperbolicObserverExpansionChapterTasteGate :
    ChapterTasteGate HyperbolicObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicObserverExpansionFromEventFlow
        (hyperbolicObserverExpansionToEventFlow x) = some x
    exact HyperbolicObserverExpansionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicObserverExpansionToEventFlow_injective heq)

instance hyperbolicObserverExpansionFieldFaithful :
    FieldFaithful HyperbolicObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicObserverExpansionFields
  field_faithful := by
    intro x y h
    cases x with
    | mk V₁ B₁ M₁ S₁ R₁ Q₁ F₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk V₂ B₂ M₂ S₂ R₂ Q₂ F₂ H₂ C₂ P₂ N₂ =>
            injection h with hV t1
            injection t1 with hB t2
            injection t2 with hM t3
            injection t3 with hS t4
            injection t4 with hR t5
            injection t5 with hQ t6
            injection t6 with hF t7
            injection t7 with hH t8
            injection t8 with hC t9
            injection t9 with hP t10
            injection t10 with hN _
            subst hV
            subst hB
            subst hM
            subst hS
            subst hR
            subst hQ
            subst hF
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance hyperbolicObserverExpansionNontrivial :
    Nontrivial HyperbolicObserverExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicObserverExpansionUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicObserverExpansionUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicObserverExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicObserverExpansionChapterTasteGate

theorem HyperbolicObserverExpansionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hyperbolicObserverExpansionDecodeBHist
        (hyperbolicObserverExpansionEncodeBHist h) = h) /\
      (forall x : HyperbolicObserverExpansionUp,
        hyperbolicObserverExpansionFromEventFlow
          (hyperbolicObserverExpansionToEventFlow x) = some x) /\
        (forall x y : HyperbolicObserverExpansionUp,
          hyperbolicObserverExpansionToEventFlow x =
            hyperbolicObserverExpansionToEventFlow y -> x = y) /\
          hyperbolicObserverExpansionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨HyperbolicObserverExpansionTasteGate_single_carrier_alignment_decode_encode,
      HyperbolicObserverExpansionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HyperbolicObserverExpansionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HyperbolicObserverExpansionUp
