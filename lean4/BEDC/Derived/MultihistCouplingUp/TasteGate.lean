import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MultihistCouplingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MultihistCouplingUp : Type where
  | mk (H0 H1 J S T C P N : BHist) : MultihistCouplingUp
  deriving DecidableEq

private def multihistCouplingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: multihistCouplingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: multihistCouplingEncodeBHist h

private def multihistCouplingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (multihistCouplingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (multihistCouplingDecodeBHist tail)

private theorem multihistCoupling_decode_encode_bhist :
    ∀ h : BHist, multihistCouplingDecodeBHist (multihistCouplingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def multihistCouplingToEventFlow :
    MultihistCouplingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MultihistCouplingUp.mk H0 H1 J S T C P N =>
      [[BMark.b0], multihistCouplingEncodeBHist H0,
        [BMark.b1, BMark.b0], multihistCouplingEncodeBHist H1,
        [BMark.b1, BMark.b1, BMark.b0], multihistCouplingEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], multihistCouplingEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multihistCouplingEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multihistCouplingEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multihistCouplingEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        multihistCouplingEncodeBHist N]

private def multihistCouplingFromEventFlow :
    EventFlow → Option MultihistCouplingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | H0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | H1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | J :: rest5 =>
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
                                      | T :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
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
                                                                        (MultihistCouplingUp.mk
                                                                          (multihistCouplingDecodeBHist
                                                                            H0)
                                                                          (multihistCouplingDecodeBHist
                                                                            H1)
                                                                          (multihistCouplingDecodeBHist
                                                                            J)
                                                                          (multihistCouplingDecodeBHist
                                                                            S)
                                                                          (multihistCouplingDecodeBHist
                                                                            T)
                                                                          (multihistCouplingDecodeBHist
                                                                            C)
                                                                          (multihistCouplingDecodeBHist
                                                                            P)
                                                                          (multihistCouplingDecodeBHist
                                                                            N))
                                                                  | _ :: _ => none

private theorem multihistCoupling_round_trip :
    ∀ x : MultihistCouplingUp,
      multihistCouplingFromEventFlow (multihistCouplingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H0 H1 J S T C P N =>
      change
        some
          (MultihistCouplingUp.mk
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist H0))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist H1))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist J))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist S))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist T))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist C))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist P))
            (multihistCouplingDecodeBHist (multihistCouplingEncodeBHist N))) =
          some (MultihistCouplingUp.mk H0 H1 J S T C P N)
      rw [multihistCoupling_decode_encode_bhist H0,
        multihistCoupling_decode_encode_bhist H1,
        multihistCoupling_decode_encode_bhist J,
        multihistCoupling_decode_encode_bhist S,
        multihistCoupling_decode_encode_bhist T,
        multihistCoupling_decode_encode_bhist C,
        multihistCoupling_decode_encode_bhist P,
        multihistCoupling_decode_encode_bhist N]

private theorem multihistCouplingToEventFlow_injective {x y : MultihistCouplingUp} :
    multihistCouplingToEventFlow x = multihistCouplingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      multihistCouplingFromEventFlow (multihistCouplingToEventFlow x) =
        multihistCouplingFromEventFlow (multihistCouplingToEventFlow y) :=
    congrArg multihistCouplingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (multihistCoupling_round_trip x).symm
      (Eq.trans hread (multihistCoupling_round_trip y)))

private def multihistCouplingFields :
    MultihistCouplingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MultihistCouplingUp.mk H0 H1 J S T C P N => [H0, H1, J, S, T, C, P, N]

private theorem multihistCoupling_field_faithful :
    ∀ x y : MultihistCouplingUp,
      multihistCouplingFields x = multihistCouplingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H0 H1 J S T C P N =>
      cases y with
      | mk H0' H1' J' S' T' C' P' N' =>
          cases hfields
          rfl

instance multihistCouplingBHistCarrier :
    BHistCarrier MultihistCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := multihistCouplingToEventFlow
  fromEventFlow := multihistCouplingFromEventFlow

instance multihistCouplingChapterTasteGate :
    ChapterTasteGate MultihistCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      multihistCouplingFromEventFlow
        (multihistCouplingToEventFlow x) = some x
    exact multihistCoupling_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (multihistCouplingToEventFlow_injective heq)

instance multihistCouplingFieldFaithful :
    FieldFaithful MultihistCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := multihistCouplingFields
  field_faithful := multihistCoupling_field_faithful

instance multihistCouplingNontrivial :
    Nontrivial MultihistCouplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MultihistCouplingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MultihistCouplingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MultihistCouplingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  multihistCouplingChapterTasteGate

theorem MultihistCouplingTasteGate_single_carrier_alignment :
    (∀ x : MultihistCouplingUp,
      multihistCouplingFromEventFlow
        (multihistCouplingToEventFlow x) = some x) ∧
      (∀ x y : MultihistCouplingUp,
        multihistCouplingToEventFlow x =
          multihistCouplingToEventFlow y → x = y) ∧
      multihistCouplingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨multihistCoupling_round_trip,
      fun _ _ => multihistCouplingToEventFlow_injective, rfl⟩

end BEDC.Derived.MultihistCouplingUp.TasteGate
