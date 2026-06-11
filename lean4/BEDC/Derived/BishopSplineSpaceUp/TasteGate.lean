import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopSplineSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopSplineSpaceUp : Type where
  | mk (G C P R E H T Q N : BHist) : BishopSplineSpaceUp
  deriving DecidableEq

def bishopSplineSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopSplineSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopSplineSpaceEncodeBHist h

def bishopSplineSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopSplineSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopSplineSpaceDecodeBHist tail)

private theorem BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopSplineSpaceFields : BishopSplineSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSplineSpaceUp.mk G C P R E H T Q N => [G, C, P, R, E, H, T, Q, N]

def bishopSplineSpaceToEventFlow : BishopSplineSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopSplineSpaceFields x).map bishopSplineSpaceEncodeBHist

def bishopSplineSpaceFromEventFlow : EventFlow -> Option BishopSplineSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | P :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | T :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BishopSplineSpaceUp.mk
                                              (bishopSplineSpaceDecodeBHist G)
                                              (bishopSplineSpaceDecodeBHist C)
                                              (bishopSplineSpaceDecodeBHist P)
                                              (bishopSplineSpaceDecodeBHist R)
                                              (bishopSplineSpaceDecodeBHist E)
                                              (bishopSplineSpaceDecodeBHist H)
                                              (bishopSplineSpaceDecodeBHist T)
                                              (bishopSplineSpaceDecodeBHist Q)
                                              (bishopSplineSpaceDecodeBHist N))
                                      | _ :: _ => none

private theorem BishopSplineSpaceTasteGate_single_carrier_alignment_round_trip :
    forall x : BishopSplineSpaceUp,
      bishopSplineSpaceFromEventFlow (bishopSplineSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G C P R E H T Q N =>
      change
        some
          (BishopSplineSpaceUp.mk
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist G))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist C))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist P))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist R))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist E))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist H))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist T))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist Q))
            (bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist N))) =
          some (BishopSplineSpaceUp.mk G C P R E H T Q N)
      rw [BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode G,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode C,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode P,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode R,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode E,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode H,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode T,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopSplineSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopSplineSpaceUp} :
    bishopSplineSpaceToEventFlow x = bishopSplineSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopSplineSpaceFromEventFlow (bishopSplineSpaceToEventFlow x) =
        bishopSplineSpaceFromEventFlow (bishopSplineSpaceToEventFlow y) :=
    congrArg bishopSplineSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopSplineSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopSplineSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopSplineSpaceTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : BishopSplineSpaceUp,
      bishopSplineSpaceFields x = bishopSplineSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 C1 P1 R1 E1 H1 T1 Q1 N1 =>
      cases y with
      | mk G2 C2 P2 R2 E2 H2 T2 Q2 N2 =>
          cases hfields
          rfl

instance bishopSplineSpaceBHistCarrier : BHistCarrier BishopSplineSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopSplineSpaceToEventFlow
  fromEventFlow := bishopSplineSpaceFromEventFlow

instance bishopSplineSpaceChapterTasteGate : ChapterTasteGate BishopSplineSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopSplineSpaceFromEventFlow (bishopSplineSpaceToEventFlow x) = some x
    exact BishopSplineSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopSplineSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopSplineSpaceFieldFaithful : FieldFaithful BishopSplineSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopSplineSpaceFields
  field_faithful := BishopSplineSpaceTasteGate_single_carrier_alignment_fields_faithful

instance bishopSplineSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopSplineSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopSplineSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopSplineSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def bishopSplineSpaceTasteGate : ChapterTasteGate BishopSplineSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopSplineSpaceChapterTasteGate

theorem BishopSplineSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopSplineSpaceUp) ∧
      (∀ h : BHist,
        bishopSplineSpaceDecodeBHist (bishopSplineSpaceEncodeBHist h) = h) ∧
        (∀ x : BishopSplineSpaceUp,
          bishopSplineSpaceFromEventFlow (bishopSplineSpaceToEventFlow x) = some x) ∧
          bishopSplineSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨bishopSplineSpaceChapterTasteGate⟩
  · constructor
    · exact BishopSplineSpaceTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · exact BishopSplineSpaceTasteGate_single_carrier_alignment_round_trip
      · rfl

end BEDC.Derived.BishopSplineSpaceUp
