import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WitnessedRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WitnessedRefutationUp : Type where
  | mk :
      (h attempted refutation bottom transports continuations provenance namecert : BHist) ->
      WitnessedRefutationUp
  deriving DecidableEq

def witnessedRefutationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: witnessedRefutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: witnessedRefutationEncodeBHist h

def witnessedRefutationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (witnessedRefutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (witnessedRefutationDecodeBHist tail)

private theorem witnessedRefutationDecode_encode_bhist :
    forall h : BHist,
      witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def witnessedRefutationToEventFlow : WitnessedRefutationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WitnessedRefutationUp.mk h attempted refutation bottom transports continuations
      provenance namecert =>
      [[BMark.b0],
        witnessedRefutationEncodeBHist h,
        [BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist attempted,
        [BMark.b1, BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist refutation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist bottom,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist continuations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedRefutationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        witnessedRefutationEncodeBHist namecert]

def witnessedRefutationFromEventFlow : EventFlow -> Option WitnessedRefutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | h :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | attempted :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refutation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | bottom :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuations :: rest11 =>
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
                                                              | namecert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (WitnessedRefutationUp.mk
                                                                          (witnessedRefutationDecodeBHist
                                                                            h)
                                                                          (witnessedRefutationDecodeBHist
                                                                            attempted)
                                                                          (witnessedRefutationDecodeBHist
                                                                            refutation)
                                                                          (witnessedRefutationDecodeBHist
                                                                            bottom)
                                                                          (witnessedRefutationDecodeBHist
                                                                            transports)
                                                                          (witnessedRefutationDecodeBHist
                                                                            continuations)
                                                                          (witnessedRefutationDecodeBHist
                                                                            provenance)
                                                                          (witnessedRefutationDecodeBHist
                                                                            namecert))
                                                                  | _ :: _ => none

private theorem witnessedRefutation_round_trip :
    forall x : WitnessedRefutationUp,
      witnessedRefutationFromEventFlow (witnessedRefutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk h attempted refutation bottom transports continuations provenance namecert =>
      change
        some
          (WitnessedRefutationUp.mk
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist h))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist attempted))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist refutation))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist bottom))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist transports))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist continuations))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist provenance))
            (witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist namecert))) =
          some
            (WitnessedRefutationUp.mk h attempted refutation bottom transports continuations
              provenance namecert)
      rw [witnessedRefutationDecode_encode_bhist h,
        witnessedRefutationDecode_encode_bhist attempted,
        witnessedRefutationDecode_encode_bhist refutation,
        witnessedRefutationDecode_encode_bhist bottom,
        witnessedRefutationDecode_encode_bhist transports,
        witnessedRefutationDecode_encode_bhist continuations,
        witnessedRefutationDecode_encode_bhist provenance,
        witnessedRefutationDecode_encode_bhist namecert]

private theorem witnessedRefutationToEventFlow_injective {x y : WitnessedRefutationUp} :
    witnessedRefutationToEventFlow x = witnessedRefutationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      witnessedRefutationFromEventFlow (witnessedRefutationToEventFlow x) =
        witnessedRefutationFromEventFlow (witnessedRefutationToEventFlow y) :=
    congrArg witnessedRefutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (witnessedRefutation_round_trip x).symm
      (Eq.trans hread (witnessedRefutation_round_trip y)))

instance witnessedRefutationBHistCarrier : BHistCarrier WitnessedRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := witnessedRefutationToEventFlow
  fromEventFlow := witnessedRefutationFromEventFlow

instance witnessedRefutationChapterTasteGate : ChapterTasteGate WitnessedRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change witnessedRefutationFromEventFlow (witnessedRefutationToEventFlow x) = some x
    exact witnessedRefutation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (witnessedRefutationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate WitnessedRefutationUp :=
  witnessedRefutationChapterTasteGate

theorem WitnessedRefutationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      witnessedRefutationDecodeBHist (witnessedRefutationEncodeBHist h) = h) /\
      (forall x : WitnessedRefutationUp,
        witnessedRefutationFromEventFlow (witnessedRefutationToEventFlow x) = some x) /\
        (forall x y : WitnessedRefutationUp,
          witnessedRefutationToEventFlow x = witnessedRefutationToEventFlow y -> x = y) /\
          witnessedRefutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact witnessedRefutationDecode_encode_bhist
  · constructor
    · exact witnessedRefutation_round_trip
    · constructor
      · intro x y heq
        exact witnessedRefutationToEventFlow_injective heq
      · rfl

end BEDC.Derived.WitnessedRefutationUp
