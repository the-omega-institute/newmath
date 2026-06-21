import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalUniformContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalUniformContinuityUp : Type where
  | mk (J F N M W Q E H C P L : BHist) : CompactIntervalUniformContinuityUp
  deriving DecidableEq

def compactIntervalUniformContinuityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalUniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalUniformContinuityEncodeBHist h

def compactIntervalUniformContinuityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalUniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalUniformContinuityDecodeBHist tail)

private theorem compactIntervalUniformContinuity_decode_encode_bhist :
    forall h : BHist,
      compactIntervalUniformContinuityDecodeBHist
        (compactIntervalUniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactIntervalUniformContinuityFields :
    CompactIntervalUniformContinuityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalUniformContinuityUp.mk J F N M W Q E H C P L =>
      [J, F, N, M, W, Q, E, H, C, P, L]

def compactIntervalUniformContinuityToEventFlow :
    CompactIntervalUniformContinuityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactIntervalUniformContinuityFields x).map
        compactIntervalUniformContinuityEncodeBHist

def compactIntervalUniformContinuityFromEventFlow :
    EventFlow -> Option CompactIntervalUniformContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | J :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | N :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | L :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompactIntervalUniformContinuityUp.mk
                                                      (compactIntervalUniformContinuityDecodeBHist J)
                                                      (compactIntervalUniformContinuityDecodeBHist F)
                                                      (compactIntervalUniformContinuityDecodeBHist N)
                                                      (compactIntervalUniformContinuityDecodeBHist M)
                                                      (compactIntervalUniformContinuityDecodeBHist W)
                                                      (compactIntervalUniformContinuityDecodeBHist Q)
                                                      (compactIntervalUniformContinuityDecodeBHist E)
                                                      (compactIntervalUniformContinuityDecodeBHist H)
                                                      (compactIntervalUniformContinuityDecodeBHist C)
                                                      (compactIntervalUniformContinuityDecodeBHist P)
                                                      (compactIntervalUniformContinuityDecodeBHist L))
                                              | _ :: _ => none

private theorem compactIntervalUniformContinuity_round_trip :
    forall x : CompactIntervalUniformContinuityUp,
      compactIntervalUniformContinuityFromEventFlow
        (compactIntervalUniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J F N M W Q E H C P L =>
      change
        some
          (CompactIntervalUniformContinuityUp.mk
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist J))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist F))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist N))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist M))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist W))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist Q))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist E))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist H))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist C))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist P))
            (compactIntervalUniformContinuityDecodeBHist
              (compactIntervalUniformContinuityEncodeBHist L))) =
          some (CompactIntervalUniformContinuityUp.mk J F N M W Q E H C P L)
      rw [compactIntervalUniformContinuity_decode_encode_bhist J,
        compactIntervalUniformContinuity_decode_encode_bhist F,
        compactIntervalUniformContinuity_decode_encode_bhist N,
        compactIntervalUniformContinuity_decode_encode_bhist M,
        compactIntervalUniformContinuity_decode_encode_bhist W,
        compactIntervalUniformContinuity_decode_encode_bhist Q,
        compactIntervalUniformContinuity_decode_encode_bhist E,
        compactIntervalUniformContinuity_decode_encode_bhist H,
        compactIntervalUniformContinuity_decode_encode_bhist C,
        compactIntervalUniformContinuity_decode_encode_bhist P,
        compactIntervalUniformContinuity_decode_encode_bhist L]

private theorem compactIntervalUniformContinuityToEventFlow_injective
    {x y : CompactIntervalUniformContinuityUp} :
    compactIntervalUniformContinuityToEventFlow x =
        compactIntervalUniformContinuityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalUniformContinuityFromEventFlow
          (compactIntervalUniformContinuityToEventFlow x) =
        compactIntervalUniformContinuityFromEventFlow
          (compactIntervalUniformContinuityToEventFlow y) :=
    congrArg compactIntervalUniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactIntervalUniformContinuity_round_trip x).symm
      (Eq.trans hread (compactIntervalUniformContinuity_round_trip y)))

private theorem compactIntervalUniformContinuity_field_faithful :
    forall x y : CompactIntervalUniformContinuityUp,
      compactIntervalUniformContinuityFields x =
        compactIntervalUniformContinuityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk J1 F1 N1 M1 W1 Q1 E1 H1 C1 P1 L1 =>
      cases y with
      | mk J2 F2 N2 M2 W2 Q2 E2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance compactIntervalUniformContinuityBHistCarrier :
    BHistCarrier CompactIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalUniformContinuityToEventFlow
  fromEventFlow := compactIntervalUniformContinuityFromEventFlow

instance compactIntervalUniformContinuityChapterTasteGate :
    ChapterTasteGate CompactIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalUniformContinuityFromEventFlow
          (compactIntervalUniformContinuityToEventFlow x) =
        some x
    exact compactIntervalUniformContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactIntervalUniformContinuityToEventFlow_injective heq)

instance compactIntervalUniformContinuityFieldFaithful :
    FieldFaithful CompactIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactIntervalUniformContinuityFields
  field_faithful := compactIntervalUniformContinuity_field_faithful

instance compactIntervalUniformContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactIntervalUniformContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactIntervalUniformContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactIntervalUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalUniformContinuityChapterTasteGate

theorem CompactIntervalUniformContinuityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactIntervalUniformContinuityDecodeBHist
        (compactIntervalUniformContinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactIntervalUniformContinuityUp) ∧
        Nonempty (ChapterTasteGate CompactIntervalUniformContinuityUp) ∧
          compactIntervalUniformContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨compactIntervalUniformContinuity_decode_encode_bhist,
      ⟨compactIntervalUniformContinuityBHistCarrier⟩,
      ⟨compactIntervalUniformContinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactIntervalUniformContinuityUp
