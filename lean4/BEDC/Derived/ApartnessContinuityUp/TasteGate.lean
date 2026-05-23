import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessContinuityUp : Type where
  | mk (G L R M S Q D E H C P N : BHist) : ApartnessContinuityUp
  deriving DecidableEq

def apartnessContinuityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessContinuityEncodeBHist h

def apartnessContinuityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessContinuityDecodeBHist tail)

private theorem ApartnessContinuityTasteGate_single_carrier_alignment_decode :
    forall h : BHist, apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessContinuityFields : ApartnessContinuityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessContinuityUp.mk G L R M S Q D E H C P N => [G, L, R, M, S, Q, D, E, H, C, P, N]

def apartnessContinuityToEventFlow : ApartnessContinuityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apartnessContinuityFields x).map apartnessContinuityEncodeBHist

def apartnessContinuityFromEventFlow : EventFlow -> Option ApartnessContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ApartnessContinuityUp.mk
                                                          (apartnessContinuityDecodeBHist G)
                                                          (apartnessContinuityDecodeBHist L)
                                                          (apartnessContinuityDecodeBHist R)
                                                          (apartnessContinuityDecodeBHist M)
                                                          (apartnessContinuityDecodeBHist S)
                                                          (apartnessContinuityDecodeBHist Q)
                                                          (apartnessContinuityDecodeBHist D)
                                                          (apartnessContinuityDecodeBHist E)
                                                          (apartnessContinuityDecodeBHist H)
                                                          (apartnessContinuityDecodeBHist C)
                                                          (apartnessContinuityDecodeBHist P)
                                                          (apartnessContinuityDecodeBHist N))
                                                  | _ :: _ => none

private theorem ApartnessContinuityTasteGate_single_carrier_alignment_round_trip :
    forall x : ApartnessContinuityUp,
      apartnessContinuityFromEventFlow (apartnessContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G L R M S Q D E H C P N =>
      change
        some
          (ApartnessContinuityUp.mk
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist G))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist L))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist R))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist M))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist S))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist Q))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist D))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist E))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist H))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist C))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist P))
            (apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist N))) =
          some (ApartnessContinuityUp.mk G L R M S Q D E H C P N)
      rw [ApartnessContinuityTasteGate_single_carrier_alignment_decode G,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode L,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode R,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode M,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode S,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode Q,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode D,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode E,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode H,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode C,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode P,
        ApartnessContinuityTasteGate_single_carrier_alignment_decode N]

private theorem ApartnessContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ApartnessContinuityUp} :
    apartnessContinuityToEventFlow x = apartnessContinuityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessContinuityFromEventFlow (apartnessContinuityToEventFlow x) =
        apartnessContinuityFromEventFlow (apartnessContinuityToEventFlow y) :=
    congrArg apartnessContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ApartnessContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ApartnessContinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem ApartnessContinuityTasteGate_single_carrier_alignment_fields :
    forall x y : ApartnessContinuityUp, apartnessContinuityFields x =
      apartnessContinuityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 L1 R1 M1 S1 Q1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk G2 L2 R2 M2 S2 Q2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance apartnessContinuityBHistCarrier : BHistCarrier ApartnessContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessContinuityToEventFlow
  fromEventFlow := apartnessContinuityFromEventFlow

instance apartnessContinuityChapterTasteGate : ChapterTasteGate ApartnessContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessContinuityFromEventFlow (apartnessContinuityToEventFlow x) = some x
    exact ApartnessContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ApartnessContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance apartnessContinuityFieldFaithful : FieldFaithful ApartnessContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apartnessContinuityFields
  field_faithful := ApartnessContinuityTasteGate_single_carrier_alignment_fields

instance apartnessContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ApartnessContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApartnessContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApartnessContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApartnessContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessContinuityChapterTasteGate

namespace TasteGate

theorem ApartnessContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ApartnessContinuityUp) ∧
      Nonempty (FieldFaithful ApartnessContinuityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ApartnessContinuityUp) ∧
          (∀ h : BHist,
            apartnessContinuityDecodeBHist (apartnessContinuityEncodeBHist h) = h) ∧
            (∀ x : ApartnessContinuityUp,
              apartnessContinuityFromEventFlow (apartnessContinuityToEventFlow x) = some x) ∧
              (∀ x y : ApartnessContinuityUp,
                apartnessContinuityToEventFlow x = apartnessContinuityToEventFlow y -> x = y) ∧
                apartnessContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨apartnessContinuityChapterTasteGate⟩
  · constructor
    · exact ⟨apartnessContinuityFieldFaithful⟩
    · constructor
      · exact ⟨apartnessContinuityNontrivial⟩
      · constructor
        · exact ApartnessContinuityTasteGate_single_carrier_alignment_decode
        · constructor
          · exact ApartnessContinuityTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact ApartnessContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate ApartnessContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.ApartnessContinuityUp.taste_gate

end TasteGate

end BEDC.Derived.ApartnessContinuityUp
