import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanBracketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanBracketUp : Type where
  | mk (R L U D S Q H C P N : BHist) : ArchimedeanBracketUp
  deriving DecidableEq

def archimedeanBracketEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanBracketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanBracketEncodeBHist h

def archimedeanBracketDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanBracketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanBracketDecodeBHist tail)

private theorem ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanBracketFields : ArchimedeanBracketUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanBracketUp.mk R L U D S Q H C P N => [R, L, U, D, S, Q, H, C, P, N]

def archimedeanBracketToEventFlow : ArchimedeanBracketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (archimedeanBracketFields x).map archimedeanBracketEncodeBHist

def archimedeanBracketFromEventFlow : EventFlow -> Option ArchimedeanBracketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ArchimedeanBracketUp.mk
                                                  (archimedeanBracketDecodeBHist R)
                                                  (archimedeanBracketDecodeBHist L)
                                                  (archimedeanBracketDecodeBHist U)
                                                  (archimedeanBracketDecodeBHist D)
                                                  (archimedeanBracketDecodeBHist S)
                                                  (archimedeanBracketDecodeBHist Q)
                                                  (archimedeanBracketDecodeBHist H)
                                                  (archimedeanBracketDecodeBHist C)
                                                  (archimedeanBracketDecodeBHist P)
                                                  (archimedeanBracketDecodeBHist N))
                                          | _ :: _ => none

private theorem ArchimedeanBracketUpTasteGate_single_carrier_alignment_round_trip :
    forall x : ArchimedeanBracketUp,
      archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R L U D S Q H C P N =>
      change
        some
          (ArchimedeanBracketUp.mk
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist R))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist L))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist U))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist D))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist S))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist Q))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist H))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist C))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist P))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist N))) =
          some (ArchimedeanBracketUp.mk R L U D S Q H C P N)
      rw [ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode R,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode L,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode U,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode D,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode S,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode Q,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode H,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode C,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode P,
        ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArchimedeanBracketUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanBracketUp} :
    archimedeanBracketToEventFlow x = archimedeanBracketToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) =
        archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow y) :=
    congrArg archimedeanBracketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArchimedeanBracketUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArchimedeanBracketUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem ArchimedeanBracketUpTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : ArchimedeanBracketUp,
      archimedeanBracketFields x = archimedeanBracketFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 L1 U1 D1 S1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 L2 U2 D2 S2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance archimedeanBracketBHistCarrier : BHistCarrier ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanBracketToEventFlow
  fromEventFlow := archimedeanBracketFromEventFlow

instance archimedeanBracketChapterTasteGate : ChapterTasteGate ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x
    exact ArchimedeanBracketUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanBracketUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance archimedeanBracketFieldFaithful : FieldFaithful ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanBracketFields
  field_faithful := ArchimedeanBracketUpTasteGate_single_carrier_alignment_fields_faithful

instance archimedeanBracketNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArchimedeanBracketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArchimedeanBracketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def archimedeanBracketTasteGate : ChapterTasteGate ArchimedeanBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanBracketChapterTasteGate

theorem ArchimedeanBracketUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ArchimedeanBracketUp) ∧
      Nonempty (FieldFaithful ArchimedeanBracketUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ArchimedeanBracketUp) ∧
          (∀ h : BHist,
            archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist h) = h) ∧
            (∀ x : ArchimedeanBracketUp,
              archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x) ∧
              (∀ x y : ArchimedeanBracketUp,
                archimedeanBracketToEventFlow x = archimedeanBracketToEventFlow y -> x = y) ∧
                archimedeanBracketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨archimedeanBracketChapterTasteGate⟩
  · constructor
    · exact ⟨archimedeanBracketFieldFaithful⟩
    · constructor
      · exact ⟨archimedeanBracketNontrivial⟩
      · constructor
        · exact ArchimedeanBracketUpTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact ArchimedeanBracketUpTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact ArchimedeanBracketUpTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.ArchimedeanBracketUp
