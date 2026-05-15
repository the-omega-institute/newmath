import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverTimeStepUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverTimeStepUp : Type where
  | mk (H D C R L P N : BHist) : ObserverTimeStepUp
  deriving DecidableEq

def observerTimeStepEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerTimeStepEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerTimeStepEncodeBHist h

def observerTimeStepDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerTimeStepDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerTimeStepDecodeBHist tail)

private theorem ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      observerTimeStepDecodeBHist
        (observerTimeStepEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerTimeStepFields :
    ObserverTimeStepUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverTimeStepUp.mk H D C R L P N => [H, D, C, R, L, P, N]

def observerTimeStepToEventFlow :
    ObserverTimeStepUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observerTimeStepFields x).map observerTimeStepEncodeBHist

def observerTimeStepFromEventFlow :
    EventFlow → Option ObserverTimeStepUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | H :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | P :: rest5 =>
                          match rest5 with
                          | [] => none
                          | N :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (ObserverTimeStepUp.mk
                                      (observerTimeStepDecodeBHist H)
                                      (observerTimeStepDecodeBHist D)
                                      (observerTimeStepDecodeBHist C)
                                      (observerTimeStepDecodeBHist R)
                                      (observerTimeStepDecodeBHist L)
                                      (observerTimeStepDecodeBHist P)
                                      (observerTimeStepDecodeBHist N))
                              | _ :: _ => none

private theorem ObserverTimeStepTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ObserverTimeStepUp,
      observerTimeStepFromEventFlow
        (observerTimeStepToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H D C R L P N =>
      change
        some
          (ObserverTimeStepUp.mk
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist H))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist D))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist C))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist R))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist L))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist P))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist N))) =
          some (ObserverTimeStepUp.mk H D C R L P N)
      rw [ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode H,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode D,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode C,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode R,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode L,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode P,
        ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode N]

private theorem ObserverTimeStepTasteGate_single_carrier_alignment_injective
    {x y : ObserverTimeStepUp} :
    observerTimeStepToEventFlow x =
      observerTimeStepToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerTimeStepFromEventFlow
          (observerTimeStepToEventFlow x) =
        observerTimeStepFromEventFlow
          (observerTimeStepToEventFlow y) :=
    congrArg observerTimeStepFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ObserverTimeStepTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ObserverTimeStepTasteGate_single_carrier_alignment_round_trip y)))

private theorem observerTimeStep_field_faithful :
    ∀ x y : ObserverTimeStepUp,
      observerTimeStepFields x = observerTimeStepFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ D₁ C₁ R₁ L₁ P₁ N₁ =>
      cases y with
      | mk H₂ D₂ C₂ R₂ L₂ P₂ N₂ =>
          cases hfields
          rfl

instance observerTimeStepBHistCarrier :
    BHistCarrier ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerTimeStepToEventFlow
  fromEventFlow := observerTimeStepFromEventFlow

instance observerTimeStepChapterTasteGate :
    ChapterTasteGate ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerTimeStepFromEventFlow
        (observerTimeStepToEventFlow x) = some x
    exact ObserverTimeStepTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ObserverTimeStepTasteGate_single_carrier_alignment_injective heq)

instance observerTimeStepFieldFaithful :
    FieldFaithful ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerTimeStepFields
  field_faithful := observerTimeStep_field_faithful

instance observerTimeStepNontrivial :
    Nontrivial ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverTimeStepUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ObserverTimeStepUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverTimeStepUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerTimeStepChapterTasteGate

theorem ObserverTimeStepTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ObserverTimeStepUp) ∧
      Nonempty (FieldFaithful ObserverTimeStepUp) ∧
        Nonempty (Nontrivial ObserverTimeStepUp) ∧
          (∀ h : BHist,
            observerTimeStepDecodeBHist
              (observerTimeStepEncodeBHist h) = h) ∧
            (∀ x : ObserverTimeStepUp,
              observerTimeStepFromEventFlow
                (observerTimeStepToEventFlow x) = some x) ∧
              (∀ x y : ObserverTimeStepUp,
                observerTimeStepToEventFlow x =
                    observerTimeStepToEventFlow y →
                  x = y) ∧
                observerTimeStepEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨observerTimeStepChapterTasteGate⟩,
      ⟨observerTimeStepFieldFaithful⟩,
      ⟨observerTimeStepNontrivial⟩,
      ObserverTimeStepTasteGate_single_carrier_alignment_decode_encode,
      ObserverTimeStepTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ObserverTimeStepTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.ObserverTimeStepUp.TasteGate
