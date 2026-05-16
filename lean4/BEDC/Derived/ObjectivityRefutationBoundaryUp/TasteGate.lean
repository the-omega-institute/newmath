import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObjectivityRefutationBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObjectivityRefutationBoundaryUp : Type where
  | mk :
      (H K A W R T P N : BHist) →
      ObjectivityRefutationBoundaryUp
  deriving DecidableEq

private def objectivityRefutationBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: objectivityRefutationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: objectivityRefutationBoundaryEncodeBHist h

private def objectivityRefutationBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (objectivityRefutationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (objectivityRefutationBoundaryDecodeBHist tail)

private theorem objectivityRefutationBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      objectivityRefutationBoundaryDecodeBHist
        (objectivityRefutationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def objectivityRefutationBoundaryToEventFlow :
    ObjectivityRefutationBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectivityRefutationBoundaryUp.mk H K A W R T P N =>
      [[BMark.b0],
        objectivityRefutationBoundaryEncodeBHist H,
        [BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectivityRefutationBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        objectivityRefutationBoundaryEncodeBHist N]

private def objectivityRefutationBoundaryFromEventFlow :
    EventFlow → Option ObjectivityRefutationBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | H :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | K :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | T :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ObjectivityRefutationBoundaryUp.mk
                                                                          (objectivityRefutationBoundaryDecodeBHist H)
                                                                          (objectivityRefutationBoundaryDecodeBHist K)
                                                                          (objectivityRefutationBoundaryDecodeBHist A)
                                                                          (objectivityRefutationBoundaryDecodeBHist W)
                                                                          (objectivityRefutationBoundaryDecodeBHist R)
                                                                          (objectivityRefutationBoundaryDecodeBHist T)
                                                                          (objectivityRefutationBoundaryDecodeBHist P)
                                                                          (objectivityRefutationBoundaryDecodeBHist N))
                                                                  | _ :: _ => none

private theorem objectivityRefutationBoundary_round_trip :
    ∀ x : ObjectivityRefutationBoundaryUp,
      objectivityRefutationBoundaryFromEventFlow
        (objectivityRefutationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H K A W R T P N =>
      change
        some
          (ObjectivityRefutationBoundaryUp.mk
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist H))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist K))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist A))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist W))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist R))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist T))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist P))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist N))) =
          some (ObjectivityRefutationBoundaryUp.mk H K A W R T P N)
      exact
        congrArg some
          (by
            rw [objectivityRefutationBoundaryDecode_encode_bhist H,
              objectivityRefutationBoundaryDecode_encode_bhist K,
              objectivityRefutationBoundaryDecode_encode_bhist A,
              objectivityRefutationBoundaryDecode_encode_bhist W,
              objectivityRefutationBoundaryDecode_encode_bhist R,
              objectivityRefutationBoundaryDecode_encode_bhist T,
              objectivityRefutationBoundaryDecode_encode_bhist P,
              objectivityRefutationBoundaryDecode_encode_bhist N])

private theorem objectivityRefutationBoundaryToEventFlow_injective
    {x y : ObjectivityRefutationBoundaryUp} :
    objectivityRefutationBoundaryToEventFlow x =
      objectivityRefutationBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow x) =
        objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow y) :=
    congrArg objectivityRefutationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (objectivityRefutationBoundary_round_trip x).symm
      (Eq.trans hread (objectivityRefutationBoundary_round_trip y)))

instance objectivityRefutationBoundaryBHistCarrier :
    BHistCarrier ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := objectivityRefutationBoundaryToEventFlow
  fromEventFlow := objectivityRefutationBoundaryFromEventFlow

instance objectivityRefutationBoundaryChapterTasteGate :
    ChapterTasteGate ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change objectivityRefutationBoundaryFromEventFlow
      (objectivityRefutationBoundaryToEventFlow x) = some x
    exact objectivityRefutationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (objectivityRefutationBoundaryToEventFlow_injective heq)

instance objectivityRefutationBoundaryFieldFaithful :
    FieldFaithful ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObjectivityRefutationBoundaryUp.mk H K A W R T P N => [H, K, A, W, R, T, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk H1 K1 A1 W1 R1 T1 P1 N1 =>
        cases y with
        | mk H2 K2 A2 W2 R2 T2 P2 N2 =>
            cases hfields
            rfl

instance objectivityRefutationBoundaryNontrivial :
    Nontrivial ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObjectivityRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObjectivityRefutationBoundaryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObjectivityRefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  objectivityRefutationBoundaryChapterTasteGate

theorem ObjectivityRefutationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      objectivityRefutationBoundaryDecodeBHist
        (objectivityRefutationBoundaryEncodeBHist h) = h) ∧
      Nonempty (Nontrivial ObjectivityRefutationBoundaryUp) ∧
        Nonempty (ChapterTasteGate ObjectivityRefutationBoundaryUp) ∧
          Nonempty (FieldFaithful ObjectivityRefutationBoundaryUp) ∧
            objectivityRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨objectivityRefutationBoundaryDecode_encode_bhist,
      ⟨⟨objectivityRefutationBoundaryNontrivial⟩,
        ⟨⟨objectivityRefutationBoundaryChapterTasteGate⟩,
          ⟨⟨objectivityRefutationBoundaryFieldFaithful⟩, rfl⟩⟩⟩⟩

end BEDC.Derived.ObjectivityRefutationBoundaryUp.TasteGate
