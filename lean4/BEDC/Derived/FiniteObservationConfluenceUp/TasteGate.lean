import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationConfluenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationConfluenceUp : Type where
  | mk (T B R E Q J H C P N : BHist) : FiniteObservationConfluenceUp
  deriving DecidableEq

def finiteObservationConfluenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationConfluenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationConfluenceEncodeBHist h

def finiteObservationConfluenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationConfluenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationConfluenceDecodeBHist tail)

private theorem finiteObservationConfluence_decode_encode :
    ∀ h : BHist,
      finiteObservationConfluenceDecodeBHist
        (finiteObservationConfluenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteObservationConfluenceToEventFlow :
    FiniteObservationConfluenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationConfluenceUp.mk T B R E Q J H C P N =>
      [finiteObservationConfluenceEncodeBHist T,
        finiteObservationConfluenceEncodeBHist B,
        finiteObservationConfluenceEncodeBHist R,
        finiteObservationConfluenceEncodeBHist E,
        finiteObservationConfluenceEncodeBHist Q,
        finiteObservationConfluenceEncodeBHist J,
        finiteObservationConfluenceEncodeBHist H,
        finiteObservationConfluenceEncodeBHist C,
        finiteObservationConfluenceEncodeBHist P,
        finiteObservationConfluenceEncodeBHist N]

def finiteObservationConfluenceFromEventFlow :
    EventFlow → Option FiniteObservationConfluenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest =>
      match rest with
      | [] => none
      | B :: rest =>
          match rest with
          | [] => none
          | R :: rest =>
              match rest with
              | [] => none
              | E :: rest =>
                  match rest with
                  | [] => none
                  | Q :: rest =>
                      match rest with
                      | [] => none
                      | J :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (FiniteObservationConfluenceUp.mk
                                                  (finiteObservationConfluenceDecodeBHist T)
                                                  (finiteObservationConfluenceDecodeBHist B)
                                                  (finiteObservationConfluenceDecodeBHist R)
                                                  (finiteObservationConfluenceDecodeBHist E)
                                                  (finiteObservationConfluenceDecodeBHist Q)
                                                  (finiteObservationConfluenceDecodeBHist J)
                                                  (finiteObservationConfluenceDecodeBHist H)
                                                  (finiteObservationConfluenceDecodeBHist C)
                                                  (finiteObservationConfluenceDecodeBHist P)
                                                  (finiteObservationConfluenceDecodeBHist N))
                                          | _ :: _ => none

private theorem finiteObservationConfluence_round_trip :
    ∀ x : FiniteObservationConfluenceUp,
      finiteObservationConfluenceFromEventFlow
        (finiteObservationConfluenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B R E Q J H C P N =>
      rw [finiteObservationConfluenceToEventFlow, finiteObservationConfluenceFromEventFlow,
        finiteObservationConfluence_decode_encode T,
        finiteObservationConfluence_decode_encode B,
        finiteObservationConfluence_decode_encode R,
        finiteObservationConfluence_decode_encode E,
        finiteObservationConfluence_decode_encode Q,
        finiteObservationConfluence_decode_encode J,
        finiteObservationConfluence_decode_encode H,
        finiteObservationConfluence_decode_encode C,
        finiteObservationConfluence_decode_encode P,
        finiteObservationConfluence_decode_encode N]

private theorem finiteObservationConfluenceToEventFlow_injective
    {x y : FiniteObservationConfluenceUp} :
    finiteObservationConfluenceToEventFlow x =
      finiteObservationConfluenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationConfluenceFromEventFlow
          (finiteObservationConfluenceToEventFlow x) =
        finiteObservationConfluenceFromEventFlow
          (finiteObservationConfluenceToEventFlow y) :=
    congrArg finiteObservationConfluenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteObservationConfluence_round_trip x).symm
      (Eq.trans hread (finiteObservationConfluence_round_trip y)))

def finiteObservationConfluenceFields :
    FiniteObservationConfluenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationConfluenceUp.mk T B R E Q J H C P N => [T, B, R, E, Q, J, H, C, P, N]

private theorem finiteObservationConfluence_field_faithful :
    ∀ x y : FiniteObservationConfluenceUp,
      finiteObservationConfluenceFields x = finiteObservationConfluenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 B1 R1 E1 Q1 J1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 B2 R2 E2 Q2 J2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteObservationConfluenceBHistCarrier :
    BHistCarrier FiniteObservationConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationConfluenceToEventFlow
  fromEventFlow := finiteObservationConfluenceFromEventFlow

instance finiteObservationConfluenceChapterTasteGate :
    ChapterTasteGate FiniteObservationConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationConfluenceFromEventFlow
        (finiteObservationConfluenceToEventFlow x) = some x
    exact finiteObservationConfluence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationConfluenceToEventFlow_injective heq)

instance finiteObservationConfluenceFieldFaithful :
    FieldFaithful FiniteObservationConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationConfluenceFields
  field_faithful := finiteObservationConfluence_field_faithful

instance finiteObservationConfluenceNontrivial :
    Nontrivial FiniteObservationConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationConfluenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteObservationConfluenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationConfluenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationConfluenceChapterTasteGate

theorem FiniteObservationConfluenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationConfluenceDecodeBHist
        (finiteObservationConfluenceEncodeBHist h) = h) ∧
      (∀ x : FiniteObservationConfluenceUp,
        finiteObservationConfluenceFromEventFlow
          (finiteObservationConfluenceToEventFlow x) = some x) ∧
      (∀ x y : FiniteObservationConfluenceUp,
        finiteObservationConfluenceToEventFlow x =
          finiteObservationConfluenceToEventFlow y -> x = y) ∧
      finiteObservationConfluenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨finiteObservationConfluence_decode_encode,
      finiteObservationConfluence_round_trip,
      fun _ _ heq => finiteObservationConfluenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteObservationConfluenceUp
