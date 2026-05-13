import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecidableRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecidableRefutationUp : Type where
  | mk :
      (proposition refutation decision exclusion transport continuation provenance name : BHist) ->
      DecidableRefutationUp
  deriving DecidableEq

def decidableRefutationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decidableRefutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decidableRefutationEncodeBHist h

def decidableRefutationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decidableRefutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decidableRefutationDecodeBHist tail)

private theorem decidableRefutationDecode_encode_bhist :
    forall h : BHist,
      decidableRefutationDecodeBHist (decidableRefutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decidableRefutationToEventFlow : DecidableRefutationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DecidableRefutationUp.mk proposition refutation decision exclusion transport continuation
      provenance name =>
      [[BMark.b0],
        decidableRefutationEncodeBHist proposition,
        [BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist refutation,
        [BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist exclusion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        decidableRefutationEncodeBHist name]

def decidableRefutationFromEventFlow : EventFlow -> Option DecidableRefutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | proposition :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refutation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | decision :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exclusion :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DecidableRefutationUp.mk
                                                                          (decidableRefutationDecodeBHist
                                                                            proposition)
                                                                          (decidableRefutationDecodeBHist
                                                                            refutation)
                                                                          (decidableRefutationDecodeBHist
                                                                            decision)
                                                                          (decidableRefutationDecodeBHist
                                                                            exclusion)
                                                                          (decidableRefutationDecodeBHist
                                                                            transport)
                                                                          (decidableRefutationDecodeBHist
                                                                            continuation)
                                                                          (decidableRefutationDecodeBHist
                                                                            provenance)
                                                                          (decidableRefutationDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem decidableRefutation_round_trip :
    forall x : DecidableRefutationUp,
      decidableRefutationFromEventFlow (decidableRefutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk proposition refutation decision exclusion transport continuation provenance name =>
      change
        some
          (DecidableRefutationUp.mk
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist proposition))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist refutation))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist decision))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist exclusion))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist transport))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist continuation))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist provenance))
            (decidableRefutationDecodeBHist (decidableRefutationEncodeBHist name))) =
          some
            (DecidableRefutationUp.mk proposition refutation decision exclusion transport
              continuation provenance name)
      rw [decidableRefutationDecode_encode_bhist proposition,
        decidableRefutationDecode_encode_bhist refutation,
        decidableRefutationDecode_encode_bhist decision,
        decidableRefutationDecode_encode_bhist exclusion,
        decidableRefutationDecode_encode_bhist transport,
        decidableRefutationDecode_encode_bhist continuation,
        decidableRefutationDecode_encode_bhist provenance,
        decidableRefutationDecode_encode_bhist name]

private theorem decidableRefutationToEventFlow_injective {x y : DecidableRefutationUp} :
    decidableRefutationToEventFlow x = decidableRefutationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decidableRefutationFromEventFlow (decidableRefutationToEventFlow x) =
        decidableRefutationFromEventFlow (decidableRefutationToEventFlow y) :=
    congrArg decidableRefutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decidableRefutation_round_trip x).symm
      (Eq.trans hread (decidableRefutation_round_trip y)))

instance decidableRefutationBHistCarrier : BHistCarrier DecidableRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decidableRefutationToEventFlow
  fromEventFlow := decidableRefutationFromEventFlow

instance decidableRefutationChapterTasteGate : ChapterTasteGate DecidableRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change decidableRefutationFromEventFlow (decidableRefutationToEventFlow x) = some x
    exact decidableRefutation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decidableRefutationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DecidableRefutationUp :=
  decidableRefutationChapterTasteGate

theorem DecidableRefutationUp_taste_gate_boundary :
    ChapterTasteGate DecidableRefutationUp /\
      (forall (x : DecidableRefutationUp) (w : RawEvent) (m : DisplayAlphabet),
        List.Mem w (BHistCarrier.toEventFlow x) ->
          List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decidableRefutationChapterTasteGate
  · intro x w m hw hm
    exact ChapterTasteGate.conservativity x w m hw hm

theorem DecidableRefutationTasteGate_single_carrier_alignment :
    (forall h : BHist, decidableRefutationDecodeBHist (decidableRefutationEncodeBHist h) = h) /\
      (forall x : DecidableRefutationUp,
        decidableRefutationFromEventFlow (decidableRefutationToEventFlow x) = some x) /\
        (forall x y : DecidableRefutationUp,
          decidableRefutationToEventFlow x = decidableRefutationToEventFlow y -> x = y) /\
          decidableRefutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decidableRefutationDecode_encode_bhist
  · constructor
    · exact decidableRefutation_round_trip
    · constructor
      · intro x y heq
        exact decidableRefutationToEventFlow_injective heq
      · rfl

end BEDC.Derived.DecidableRefutationUp
