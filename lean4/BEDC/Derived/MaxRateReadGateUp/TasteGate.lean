import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaxRateReadGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MaxRateReadGateUp : Type where
  | mk (M R S F L H Q C P N : BHist) : MaxRateReadGateUp
  deriving DecidableEq

def maxRateReadGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: maxRateReadGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: maxRateReadGateEncodeBHist h

def maxRateReadGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (maxRateReadGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (maxRateReadGateDecodeBHist tail)

private theorem maxRateReadGate_decode_encode_bhist :
    ∀ h : BHist, maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def maxRateReadGateToEventFlow : MaxRateReadGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MaxRateReadGateUp.mk M R S F L H Q C P N =>
      [[BMark.b0], maxRateReadGateEncodeBHist M,
        [BMark.b1, BMark.b0], maxRateReadGateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0], maxRateReadGateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], maxRateReadGateEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxRateReadGateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxRateReadGateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxRateReadGateEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        maxRateReadGateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        maxRateReadGateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        maxRateReadGateEncodeBHist N]

def maxRateReadGateFromEventFlow : EventFlow → Option MaxRateReadGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | F :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | Q :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MaxRateReadGateUp.mk
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            M)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            R)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            S)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            F)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            L)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            H)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            Q)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            C)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            P)
                                                                                          (maxRateReadGateDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ => none

private theorem maxRateReadGate_round_trip :
    ∀ x : MaxRateReadGateUp,
      maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R S F L H Q C P N =>
      change
        some
          (MaxRateReadGateUp.mk
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist M))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist R))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist S))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist F))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist L))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist H))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist Q))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist C))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist P))
            (maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist N))) =
          some (MaxRateReadGateUp.mk M R S F L H Q C P N)
      rw [maxRateReadGate_decode_encode_bhist M, maxRateReadGate_decode_encode_bhist R,
        maxRateReadGate_decode_encode_bhist S, maxRateReadGate_decode_encode_bhist F,
        maxRateReadGate_decode_encode_bhist L, maxRateReadGate_decode_encode_bhist H,
        maxRateReadGate_decode_encode_bhist Q, maxRateReadGate_decode_encode_bhist C,
        maxRateReadGate_decode_encode_bhist P, maxRateReadGate_decode_encode_bhist N]

private theorem maxRateReadGateToEventFlow_injective {x y : MaxRateReadGateUp} :
    maxRateReadGateToEventFlow x = maxRateReadGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow x) =
        maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow y) :=
    congrArg maxRateReadGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (maxRateReadGate_round_trip x).symm
      (Eq.trans hread (maxRateReadGate_round_trip y)))

def maxRateReadGateFields : MaxRateReadGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MaxRateReadGateUp.mk M R S F L H Q C P N => [M, R, S, F, L, H, Q, C, P, N]

private theorem maxRateReadGate_field_faithful :
    ∀ x y : MaxRateReadGateUp, maxRateReadGateFields x = maxRateReadGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M R S F L H Q C P N =>
      cases y with
      | mk M' R' S' F' L' H' Q' C' P' N' =>
          cases hfields
          rfl

instance maxRateReadGateBHistCarrier : BHistCarrier MaxRateReadGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := maxRateReadGateToEventFlow
  fromEventFlow := maxRateReadGateFromEventFlow

instance maxRateReadGateChapterTasteGate : ChapterTasteGate MaxRateReadGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow x) = some x
    exact maxRateReadGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (maxRateReadGateToEventFlow_injective heq)

instance maxRateReadGateFieldFaithful : FieldFaithful MaxRateReadGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := maxRateReadGateFields
  field_faithful := maxRateReadGate_field_faithful

instance maxRateReadGateNontrivial : Nontrivial MaxRateReadGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MaxRateReadGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MaxRateReadGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MaxRateReadGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  maxRateReadGateChapterTasteGate

theorem MaxRateReadGateTasteGate_single_carrier_alignment :
    (∀ h : BHist, maxRateReadGateDecodeBHist (maxRateReadGateEncodeBHist h) = h) ∧
      (∀ x : MaxRateReadGateUp,
        maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow x) = some x) ∧
        (∀ x y : MaxRateReadGateUp,
          maxRateReadGateToEventFlow x = maxRateReadGateToEventFlow y → x = y) ∧
          maxRateReadGateEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : MaxRateReadGateUp, maxRateReadGateFields x = maxRateReadGateFields y →
              x = y) ∧
              (∃ x y : MaxRateReadGateUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact maxRateReadGate_decode_encode_bhist
  · constructor
    · exact maxRateReadGate_round_trip
    · constructor
      · intro x y heq
        exact maxRateReadGateToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact maxRateReadGate_field_faithful
          · exact
              ⟨MaxRateReadGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                MaxRateReadGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

theorem MaxRateReadGateCarrier_symmetry_nonescape (M R S F L H Q C P N : BHist) :
    ∃ G : MaxRateReadGateUp,
      G = MaxRateReadGateUp.mk M R S F L H Q C P N ∧
        maxRateReadGateFromEventFlow (maxRateReadGateToEventFlow G) = some G ∧
          maxRateReadGateFields G = [M, R, S, F, L, H, Q, C, P, N] ∧
            maxRateReadGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  refine ⟨MaxRateReadGateUp.mk M R S F L H Q C P N, rfl, ?_, rfl, rfl⟩
  exact maxRateReadGate_round_trip (MaxRateReadGateUp.mk M R S F L H Q C P N)

end BEDC.Derived.MaxRateReadGateUp
