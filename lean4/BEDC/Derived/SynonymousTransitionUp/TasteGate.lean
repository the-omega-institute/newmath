import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SynonymousTransitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SynonymousTransitionUp : Type where
  | mk (W M A B T H C P N : BHist) : SynonymousTransitionUp
  deriving DecidableEq

def synonymousTransitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: synonymousTransitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: synonymousTransitionEncodeBHist h

def synonymousTransitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (synonymousTransitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (synonymousTransitionDecodeBHist tail)

private theorem synonymousTransitionDecode_encode_bhist :
    ∀ h : BHist, synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def synonymousTransitionFields : SynonymousTransitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SynonymousTransitionUp.mk W M A B T H C P N => [W, M, A, B, T, H, C, P, N]

def synonymousTransitionToEventFlow : SynonymousTransitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (synonymousTransitionFields x).map synonymousTransitionEncodeBHist

def synonymousTransitionFromEventFlow : EventFlow → Option SynonymousTransitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: restW =>
      match restW with
      | M :: restM =>
          match restM with
          | A :: restA =>
              match restA with
              | B :: restB =>
                  match restB with
                  | T :: restT =>
                      match restT with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (SynonymousTransitionUp.mk
                                              (synonymousTransitionDecodeBHist W)
                                              (synonymousTransitionDecodeBHist M)
                                              (synonymousTransitionDecodeBHist A)
                                              (synonymousTransitionDecodeBHist B)
                                              (synonymousTransitionDecodeBHist T)
                                              (synonymousTransitionDecodeBHist H)
                                              (synonymousTransitionDecodeBHist C)
                                              (synonymousTransitionDecodeBHist P)
                                              (synonymousTransitionDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem synonymousTransition_round_trip :
    ∀ x : SynonymousTransitionUp,
      synonymousTransitionFromEventFlow (synonymousTransitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W M A B T H C P N =>
      change
        some
          (SynonymousTransitionUp.mk
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist W))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist M))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist A))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist B))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist T))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist H))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist C))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist P))
            (synonymousTransitionDecodeBHist (synonymousTransitionEncodeBHist N))) =
          some (SynonymousTransitionUp.mk W M A B T H C P N)
      rw [synonymousTransitionDecode_encode_bhist W, synonymousTransitionDecode_encode_bhist M,
        synonymousTransitionDecode_encode_bhist A, synonymousTransitionDecode_encode_bhist B,
        synonymousTransitionDecode_encode_bhist T, synonymousTransitionDecode_encode_bhist H,
        synonymousTransitionDecode_encode_bhist C, synonymousTransitionDecode_encode_bhist P,
        synonymousTransitionDecode_encode_bhist N]

private theorem synonymousTransitionToEventFlow_injective {x y : SynonymousTransitionUp} :
    synonymousTransitionToEventFlow x = synonymousTransitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      synonymousTransitionFromEventFlow (synonymousTransitionToEventFlow x) =
        synonymousTransitionFromEventFlow (synonymousTransitionToEventFlow y) :=
    congrArg synonymousTransitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (synonymousTransition_round_trip x).symm
      (Eq.trans hread (synonymousTransition_round_trip y)))

private theorem synonymousTransition_fields_faithful :
    ∀ x y : SynonymousTransitionUp, synonymousTransitionFields x = synonymousTransitionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 M1 A1 B1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 M2 A2 B2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance synonymousTransitionBHistCarrier : BHistCarrier SynonymousTransitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := synonymousTransitionToEventFlow
  fromEventFlow := synonymousTransitionFromEventFlow

instance synonymousTransitionChapterTasteGate : ChapterTasteGate SynonymousTransitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change synonymousTransitionFromEventFlow (synonymousTransitionToEventFlow x) = some x
    exact synonymousTransition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (synonymousTransitionToEventFlow_injective heq)

instance synonymousTransitionFieldFaithful : FieldFaithful SynonymousTransitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := synonymousTransitionFields
  field_faithful := synonymousTransition_fields_faithful

instance synonymousTransitionNontrivial : BEDC.Meta.TasteGate.Nontrivial SynonymousTransitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SynonymousTransitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SynonymousTransitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SynonymousTransitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  synonymousTransitionChapterTasteGate

theorem SynonymousTransitionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SynonymousTransitionUp) ∧
      Nonempty (FieldFaithful SynonymousTransitionUp) ∧
        Nonempty (Nontrivial SynonymousTransitionUp) ∧
          (∀ x : SynonymousTransitionUp,
            synonymousTransitionFromEventFlow (synonymousTransitionToEventFlow x) = some x) ∧
            (∀ x y : SynonymousTransitionUp,
              synonymousTransitionToEventFlow x = synonymousTransitionToEventFlow y -> x = y) ∧
              synonymousTransitionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro synonymousTransitionChapterTasteGate,
      Nonempty.intro synonymousTransitionFieldFaithful,
      Nonempty.intro synonymousTransitionNontrivial,
      synonymousTransition_round_trip,
      (fun _ _ heq => synonymousTransitionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SynonymousTransitionUp
