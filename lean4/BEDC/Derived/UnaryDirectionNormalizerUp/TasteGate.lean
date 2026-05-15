import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnaryDirectionNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnaryDirectionNormalizerUp : Type where
  | mk : (A Z K D H C P N : BHist) -> UnaryDirectionNormalizerUp

def unaryDirectionNormalizerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unaryDirectionNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unaryDirectionNormalizerEncodeBHist h

def unaryDirectionNormalizerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unaryDirectionNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unaryDirectionNormalizerDecodeBHist tail)

private theorem unaryDirectionNormalizer_decode_encode_bhist :
    forall h : BHist, unaryDirectionNormalizerDecodeBHist
      (unaryDirectionNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def unaryDirectionNormalizerToEventFlow : UnaryDirectionNormalizerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryDirectionNormalizerUp.mk A Z K D H C P N =>
      [[BMark.b0],
        unaryDirectionNormalizerEncodeBHist A,
        [BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryDirectionNormalizerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        unaryDirectionNormalizerEncodeBHist N]

def unaryDirectionNormalizerFromEventFlow : EventFlow -> Option UnaryDirectionNormalizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
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
                                                                        (UnaryDirectionNormalizerUp.mk
                                                                          (unaryDirectionNormalizerDecodeBHist A)
                                                                          (unaryDirectionNormalizerDecodeBHist Z)
                                                                          (unaryDirectionNormalizerDecodeBHist K)
                                                                          (unaryDirectionNormalizerDecodeBHist D)
                                                                          (unaryDirectionNormalizerDecodeBHist H)
                                                                          (unaryDirectionNormalizerDecodeBHist C)
                                                                          (unaryDirectionNormalizerDecodeBHist P)
                                                                          (unaryDirectionNormalizerDecodeBHist N))
                                                                  | _ :: _ => none

private theorem unaryDirectionNormalizer_round_trip :
    forall x : UnaryDirectionNormalizerUp,
      unaryDirectionNormalizerFromEventFlow (unaryDirectionNormalizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Z K D H C P N =>
      change
        some
          (UnaryDirectionNormalizerUp.mk
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist A))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist Z))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist K))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist D))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist H))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist C))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist P))
            (unaryDirectionNormalizerDecodeBHist (unaryDirectionNormalizerEncodeBHist N))) =
          some (UnaryDirectionNormalizerUp.mk A Z K D H C P N)
      rw [unaryDirectionNormalizer_decode_encode_bhist A,
        unaryDirectionNormalizer_decode_encode_bhist Z,
        unaryDirectionNormalizer_decode_encode_bhist K,
        unaryDirectionNormalizer_decode_encode_bhist D,
        unaryDirectionNormalizer_decode_encode_bhist H,
        unaryDirectionNormalizer_decode_encode_bhist C,
        unaryDirectionNormalizer_decode_encode_bhist P,
        unaryDirectionNormalizer_decode_encode_bhist N]

private theorem unaryDirectionNormalizerToEventFlow_injective
    {x y : UnaryDirectionNormalizerUp} :
    unaryDirectionNormalizerToEventFlow x =
      unaryDirectionNormalizerToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unaryDirectionNormalizerFromEventFlow (unaryDirectionNormalizerToEventFlow x) =
        unaryDirectionNormalizerFromEventFlow (unaryDirectionNormalizerToEventFlow y) :=
    congrArg unaryDirectionNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unaryDirectionNormalizer_round_trip x).symm
      (Eq.trans hread (unaryDirectionNormalizer_round_trip y)))

private def unaryDirectionNormalizerFields : UnaryDirectionNormalizerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryDirectionNormalizerUp.mk A Z K D H C P N => [A, Z, K, D, H, C, P, N]

private theorem unaryDirectionNormalizer_field_faithful :
    forall x y : UnaryDirectionNormalizerUp,
      unaryDirectionNormalizerFields x = unaryDirectionNormalizerFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A Z K D H C P N =>
      cases y with
      | mk A' Z' K' D' H' C' P' N' =>
          cases hfields
          rfl

instance unaryDirectionNormalizerBHistCarrier :
    BHistCarrier UnaryDirectionNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unaryDirectionNormalizerToEventFlow
  fromEventFlow := unaryDirectionNormalizerFromEventFlow

instance unaryDirectionNormalizerChapterTasteGate :
    ChapterTasteGate UnaryDirectionNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change unaryDirectionNormalizerFromEventFlow
      (unaryDirectionNormalizerToEventFlow x) = some x
    exact unaryDirectionNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unaryDirectionNormalizerToEventFlow_injective heq)

instance unaryDirectionNormalizerFieldFaithful :
    FieldFaithful UnaryDirectionNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := unaryDirectionNormalizerFields
  field_faithful := unaryDirectionNormalizer_field_faithful

def taste_gate : ChapterTasteGate UnaryDirectionNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unaryDirectionNormalizerChapterTasteGate

theorem UnaryDirectionNormalizerTasteGate_single_carrier_alignment :
    (forall h : BHist, unaryDirectionNormalizerDecodeBHist
      (unaryDirectionNormalizerEncodeBHist h) = h) ∧
      (forall x : UnaryDirectionNormalizerUp,
        unaryDirectionNormalizerFromEventFlow
          (unaryDirectionNormalizerToEventFlow x) = some x) ∧
        (forall x y : UnaryDirectionNormalizerUp,
          unaryDirectionNormalizerToEventFlow x =
            unaryDirectionNormalizerToEventFlow y -> x = y) ∧
          unaryDirectionNormalizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨unaryDirectionNormalizer_decode_encode_bhist, unaryDirectionNormalizer_round_trip,
      (by
        intro x y heq
        exact unaryDirectionNormalizerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UnaryDirectionNormalizerUp
