import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyModulusUp : Type where
  | mk : (S R D M W E H C P N : BHist) -> UniformCauchyModulusUp
  deriving DecidableEq

def UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist h

def UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
        (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def UniformCauchyModulusTasteGate_single_carrier_alignment_fields :
    UniformCauchyModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyModulusUp.mk S R D M W E H C P N => [S, R, D, M, W, E, H, C, P, N]

def UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow :
    UniformCauchyModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (UniformCauchyModulusTasteGate_single_carrier_alignment_fields x).map
        UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist

def UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option UniformCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (UniformCauchyModulusUp.mk
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist S)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist R)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist D)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist M)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist W)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist E)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist H)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist C)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist P)
                                                  (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist N))
                                          | _ :: _ => none

private theorem UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip :
    forall x : UniformCauchyModulusUp,
      UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
        (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M W E H C P N =>
      change
        some
          (UniformCauchyModulusUp.mk
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist S))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist R))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist D))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist M))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist W))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist E))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist H))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist C))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist P))
            (UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
              (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (UniformCauchyModulusUp.mk S R D M W E H C P N)
      rw [UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode S,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode R,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode D,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode M,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode W,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode E,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode H,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode C,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode P,
        UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchyModulusUp} :
    UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x =
      UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread : some x = some y := by
    calc
      some x =
          UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
            (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x) :=
        (UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
            (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hread

private theorem UniformCauchyModulusTasteGate_single_carrier_alignment_field_faithful :
    forall x y : UniformCauchyModulusUp,
      UniformCauchyModulusTasteGate_single_carrier_alignment_fields x =
        UniformCauchyModulusTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 M1 W1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 M2 W2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformCauchyModulusBHistCarrier : BHistCarrier UniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow

instance uniformCauchyModulusChapterTasteGate :
    ChapterTasteGate UniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
        (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformCauchyModulusFieldFaithful : FieldFaithful UniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := UniformCauchyModulusTasteGate_single_carrier_alignment_fields
  field_faithful := UniformCauchyModulusTasteGate_single_carrier_alignment_field_faithful

instance uniformCauchyModulusNontrivial : Nontrivial UniformCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchyModulusChapterTasteGate

theorem UniformCauchyModulusTasteGate_e0_row_round_trip
    (S R D M W E H C P N : BHist) :
    UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
      (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow
        (UniformCauchyModulusUp.mk (BHist.e0 S) R D M W E H C P N)) =
      some (UniformCauchyModulusUp.mk (BHist.e0 S) R D M W E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip
    (UniformCauchyModulusUp.mk (BHist.e0 S) R D M W E H C P N)

theorem UniformCauchyModulusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      UniformCauchyModulusTasteGate_single_carrier_alignment_decodeBHist
        (UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      (∀ x : UniformCauchyModulusUp,
        UniformCauchyModulusTasteGate_single_carrier_alignment_fromEventFlow
          (UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
      (∀ x y : UniformCauchyModulusUp,
        UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow x =
          UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow y -> x = y) ∧
      UniformCauchyModulusTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact UniformCauchyModulusTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact UniformCauchyModulusTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact UniformCauchyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.UniformCauchyModulusUp
