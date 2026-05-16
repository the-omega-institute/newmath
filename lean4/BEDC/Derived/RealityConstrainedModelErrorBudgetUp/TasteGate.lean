import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedModelErrorBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedModelErrorBudgetUp : Type where
  | mk (S E O M F H C P N : BHist) : RealityConstrainedModelErrorBudgetUp
  deriving DecidableEq

def realityConstrainedModelErrorBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedModelErrorBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedModelErrorBudgetEncodeBHist h

def realityConstrainedModelErrorBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedModelErrorBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedModelErrorBudgetDecodeBHist tail)

private theorem realityConstrainedModelErrorBudget_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedModelErrorBudgetDecodeBHist
        (realityConstrainedModelErrorBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedModelErrorBudget_mk_congr
    {S S' E E' O O' M M' F F' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hE : E' = E)
    (hO : O' = O)
    (hM : M' = M)
    (hF : F' = F)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RealityConstrainedModelErrorBudgetUp.mk S' E' O' M' F' H' C' P' N' =
      RealityConstrainedModelErrorBudgetUp.mk S E O M F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hE
  cases hO
  cases hM
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realityConstrainedModelErrorBudgetToEventFlow :
    RealityConstrainedModelErrorBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedModelErrorBudgetUp.mk S E O M F H C P N =>
      [[BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist S,
        [BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedModelErrorBudgetEncodeBHist N]

private def realityConstrainedModelErrorBudgetDecodePacket
    (S E O M F H C P N : RawEvent) : RealityConstrainedModelErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealityConstrainedModelErrorBudgetUp.mk
    (realityConstrainedModelErrorBudgetDecodeBHist S)
    (realityConstrainedModelErrorBudgetDecodeBHist E)
    (realityConstrainedModelErrorBudgetDecodeBHist O)
    (realityConstrainedModelErrorBudgetDecodeBHist M)
    (realityConstrainedModelErrorBudgetDecodeBHist F)
    (realityConstrainedModelErrorBudgetDecodeBHist H)
    (realityConstrainedModelErrorBudgetDecodeBHist C)
    (realityConstrainedModelErrorBudgetDecodeBHist P)
    (realityConstrainedModelErrorBudgetDecodeBHist N)

def realityConstrainedModelErrorBudgetFromEventFlow :
    EventFlow → Option RealityConstrainedModelErrorBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | O :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | F :: rest9 =>
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
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (realityConstrainedModelErrorBudgetDecodePacket
                                                                                  S E O M F H C P N)
                                                                          | _ :: _ => none

private theorem realityConstrainedModelErrorBudget_round_trip :
    ∀ x : RealityConstrainedModelErrorBudgetUp,
      realityConstrainedModelErrorBudgetFromEventFlow
        (realityConstrainedModelErrorBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S E O M F H C P N =>
      change
        some
          (realityConstrainedModelErrorBudgetDecodePacket
            (realityConstrainedModelErrorBudgetEncodeBHist S)
            (realityConstrainedModelErrorBudgetEncodeBHist E)
            (realityConstrainedModelErrorBudgetEncodeBHist O)
            (realityConstrainedModelErrorBudgetEncodeBHist M)
            (realityConstrainedModelErrorBudgetEncodeBHist F)
            (realityConstrainedModelErrorBudgetEncodeBHist H)
            (realityConstrainedModelErrorBudgetEncodeBHist C)
            (realityConstrainedModelErrorBudgetEncodeBHist P)
            (realityConstrainedModelErrorBudgetEncodeBHist N)) =
          some (RealityConstrainedModelErrorBudgetUp.mk S E O M F H C P N)
      unfold realityConstrainedModelErrorBudgetDecodePacket
      exact
        congrArg some
          (realityConstrainedModelErrorBudget_mk_congr
            (realityConstrainedModelErrorBudget_decode_encode_bhist S)
            (realityConstrainedModelErrorBudget_decode_encode_bhist E)
            (realityConstrainedModelErrorBudget_decode_encode_bhist O)
            (realityConstrainedModelErrorBudget_decode_encode_bhist M)
            (realityConstrainedModelErrorBudget_decode_encode_bhist F)
            (realityConstrainedModelErrorBudget_decode_encode_bhist H)
            (realityConstrainedModelErrorBudget_decode_encode_bhist C)
            (realityConstrainedModelErrorBudget_decode_encode_bhist P)
            (realityConstrainedModelErrorBudget_decode_encode_bhist N))

private theorem realityConstrainedModelErrorBudgetToEventFlow_injective
    {x y : RealityConstrainedModelErrorBudgetUp} :
    realityConstrainedModelErrorBudgetToEventFlow x =
      realityConstrainedModelErrorBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedModelErrorBudgetFromEventFlow
          (realityConstrainedModelErrorBudgetToEventFlow x) =
        realityConstrainedModelErrorBudgetFromEventFlow
          (realityConstrainedModelErrorBudgetToEventFlow y) :=
    congrArg realityConstrainedModelErrorBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedModelErrorBudget_round_trip x).symm
      (Eq.trans hread (realityConstrainedModelErrorBudget_round_trip y)))

private def realityConstrainedModelErrorBudgetFields :
    RealityConstrainedModelErrorBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedModelErrorBudgetUp.mk S E O M F H C P N =>
      [S, E, O, M, F, H, C, P, N]

private theorem realityConstrainedModelErrorBudget_field_faithful :
    ∀ x y : RealityConstrainedModelErrorBudgetUp,
      realityConstrainedModelErrorBudgetFields x =
        realityConstrainedModelErrorBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S E O M F H C P N =>
      cases y with
      | mk S' E' O' M' F' H' C' P' N' =>
          cases hfields
          rfl

instance realityConstrainedModelErrorBudgetBHistCarrier :
    BHistCarrier RealityConstrainedModelErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedModelErrorBudgetToEventFlow
  fromEventFlow := realityConstrainedModelErrorBudgetFromEventFlow

instance realityConstrainedModelErrorBudgetChapterTasteGate :
    ChapterTasteGate RealityConstrainedModelErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedModelErrorBudgetFromEventFlow
        (realityConstrainedModelErrorBudgetToEventFlow x) = some x
    exact realityConstrainedModelErrorBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedModelErrorBudgetToEventFlow_injective heq)

instance realityConstrainedModelErrorBudgetFieldFaithful :
    FieldFaithful RealityConstrainedModelErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedModelErrorBudgetFields
  field_faithful := realityConstrainedModelErrorBudget_field_faithful

instance realityConstrainedModelErrorBudgetNontrivial :
    Nontrivial RealityConstrainedModelErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedModelErrorBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedModelErrorBudgetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedModelErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedModelErrorBudgetChapterTasteGate

theorem RealityConstrainedModelErrorBudgetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealityConstrainedModelErrorBudgetUp) ∧
      Nonempty (FieldFaithful RealityConstrainedModelErrorBudgetUp) ∧
        Nonempty (Nontrivial RealityConstrainedModelErrorBudgetUp) ∧
          (∀ h : BHist,
            realityConstrainedModelErrorBudgetDecodeBHist
              (realityConstrainedModelErrorBudgetEncodeBHist h) = h) ∧
            (∀ x : RealityConstrainedModelErrorBudgetUp,
              realityConstrainedModelErrorBudgetFromEventFlow
                (realityConstrainedModelErrorBudgetToEventFlow x) = some x) ∧
              (∀ x y : RealityConstrainedModelErrorBudgetUp,
                realityConstrainedModelErrorBudgetToEventFlow x =
                    realityConstrainedModelErrorBudgetToEventFlow y →
                  x = y) ∧
                realityConstrainedModelErrorBudgetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨realityConstrainedModelErrorBudgetChapterTasteGate⟩,
      ⟨realityConstrainedModelErrorBudgetFieldFaithful⟩,
      ⟨realityConstrainedModelErrorBudgetNontrivial⟩,
      realityConstrainedModelErrorBudget_decode_encode_bhist,
      realityConstrainedModelErrorBudget_round_trip,
      (fun _ _ heq => realityConstrainedModelErrorBudgetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealityConstrainedModelErrorBudgetUp
