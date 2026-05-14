import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FableMachineBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FableMachineBoundaryUp : Type where
  | mk (H E L S W K T C P N : BHist) : FableMachineBoundaryUp
  deriving DecidableEq

private def fableMachineBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fableMachineBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fableMachineBoundaryEncodeBHist h

private def fableMachineBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fableMachineBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fableMachineBoundaryDecodeBHist tail)

private theorem fableMachineBoundary_decode_encode_bhist :
    ∀ h : BHist,
      fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def fableMachineBoundaryToEventFlow :
    FableMachineBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FableMachineBoundaryUp.mk H E L S W K T C P N =>
      [[BMark.b0], fableMachineBoundaryEncodeBHist H,
        [BMark.b1, BMark.b0], fableMachineBoundaryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0], fableMachineBoundaryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], fableMachineBoundaryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fableMachineBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist N]

private def fableMachineBoundaryFromEventFlow :
    EventFlow → Option FableMachineBoundaryUp
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
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | W :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | K :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | T :: rest13 =>
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
                                                                                        (FableMachineBoundaryUp.mk
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            H)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            E)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            L)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            S)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            W)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            K)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            T)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            C)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            P)
                                                                                          (fableMachineBoundaryDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ => none

private theorem fableMachineBoundary_round_trip :
    ∀ x : FableMachineBoundaryUp,
      fableMachineBoundaryFromEventFlow
        (fableMachineBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H E L S W K T C P N =>
      change
        some
          (FableMachineBoundaryUp.mk
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist H))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist E))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist L))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist S))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist W))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist K))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist T))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist C))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist P))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist N))) =
          some (FableMachineBoundaryUp.mk H E L S W K T C P N)
      rw [fableMachineBoundary_decode_encode_bhist H,
        fableMachineBoundary_decode_encode_bhist E,
        fableMachineBoundary_decode_encode_bhist L,
        fableMachineBoundary_decode_encode_bhist S,
        fableMachineBoundary_decode_encode_bhist W,
        fableMachineBoundary_decode_encode_bhist K,
        fableMachineBoundary_decode_encode_bhist T,
        fableMachineBoundary_decode_encode_bhist C,
        fableMachineBoundary_decode_encode_bhist P,
        fableMachineBoundary_decode_encode_bhist N]

private theorem fableMachineBoundaryToEventFlow_injective
    {x y : FableMachineBoundaryUp} :
    fableMachineBoundaryToEventFlow x =
      fableMachineBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fableMachineBoundaryFromEventFlow
          (fableMachineBoundaryToEventFlow x) =
        fableMachineBoundaryFromEventFlow
          (fableMachineBoundaryToEventFlow y) :=
    congrArg fableMachineBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fableMachineBoundary_round_trip x).symm
      (Eq.trans hread (fableMachineBoundary_round_trip y)))

private def fableMachineBoundaryFields :
    FableMachineBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FableMachineBoundaryUp.mk H E L S W K T C P N => [H, E, L, S, W, K, T, C, P, N]

private theorem fableMachineBoundary_field_faithful :
    ∀ x y : FableMachineBoundaryUp,
      fableMachineBoundaryFields x = fableMachineBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H E L S W K T C P N =>
      cases y with
      | mk H' E' L' S' W' K' T' C' P' N' =>
          cases hfields
          rfl

instance fableMachineBoundaryBHistCarrier :
    BHistCarrier FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fableMachineBoundaryToEventFlow
  fromEventFlow := fableMachineBoundaryFromEventFlow

instance fableMachineBoundaryChapterTasteGate :
    ChapterTasteGate FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fableMachineBoundaryFromEventFlow
        (fableMachineBoundaryToEventFlow x) = some x
    exact fableMachineBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableMachineBoundaryToEventFlow_injective heq)

instance fableMachineBoundaryFieldFaithful :
    FieldFaithful FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fableMachineBoundaryFields
  field_faithful := fableMachineBoundary_field_faithful

instance fableMachineBoundaryNontrivial :
    Nontrivial FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FableMachineBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FableMachineBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FableMachineBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fableMachineBoundaryChapterTasteGate

theorem FableMachineBoundaryTasteGate_single_carrier_alignment :
    (∀ x : FableMachineBoundaryUp,
      fableMachineBoundaryFromEventFlow
        (fableMachineBoundaryToEventFlow x) = some x) ∧
      (∀ x y : FableMachineBoundaryUp,
        fableMachineBoundaryToEventFlow x =
          fableMachineBoundaryToEventFlow y → x = y) ∧
      fableMachineBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨fableMachineBoundary_round_trip,
      fun _ _ => fableMachineBoundaryToEventFlow_injective, rfl⟩

end BEDC.Derived.FableMachineBoundaryUp.TasteGate
