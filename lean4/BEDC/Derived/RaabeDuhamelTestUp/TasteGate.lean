import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RaabeDuhamelTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RaabeDuhamelTestUp : Type where
  | mk (A Q M D W T E H C P N : BHist) : RaabeDuhamelTestUp
  deriving DecidableEq

def raabeDuhamelTestEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: raabeDuhamelTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: raabeDuhamelTestEncodeBHist h

def raabeDuhamelTestDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (raabeDuhamelTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (raabeDuhamelTestDecodeBHist tail)

private theorem raabeDuhamelTest_decode_encode_bhist :
    forall h : BHist, raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def raabeDuhamelTestFields : RaabeDuhamelTestUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RaabeDuhamelTestUp.mk A Q M D W T E H C P N => [A, Q, M, D, W, T, E, H, C, P, N]

def raabeDuhamelTestToEventFlow : RaabeDuhamelTestUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (raabeDuhamelTestFields x).map raabeDuhamelTestEncodeBHist

def raabeDuhamelTestFromEventFlow : EventFlow -> Option RaabeDuhamelTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
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
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RaabeDuhamelTestUp.mk
                                                      (raabeDuhamelTestDecodeBHist A)
                                                      (raabeDuhamelTestDecodeBHist Q)
                                                      (raabeDuhamelTestDecodeBHist M)
                                                      (raabeDuhamelTestDecodeBHist D)
                                                      (raabeDuhamelTestDecodeBHist W)
                                                      (raabeDuhamelTestDecodeBHist T)
                                                      (raabeDuhamelTestDecodeBHist E)
                                                      (raabeDuhamelTestDecodeBHist H)
                                                      (raabeDuhamelTestDecodeBHist C)
                                                      (raabeDuhamelTestDecodeBHist P)
                                                      (raabeDuhamelTestDecodeBHist N))
                                              | _ :: _ => none

private theorem raabeDuhamelTest_round_trip :
    forall x : RaabeDuhamelTestUp,
      raabeDuhamelTestFromEventFlow (raabeDuhamelTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q M D W T E H C P N =>
      change
        some
          (RaabeDuhamelTestUp.mk
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist A))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist Q))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist M))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist D))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist W))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist T))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist E))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist H))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist C))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist P))
            (raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist N))) =
          some (RaabeDuhamelTestUp.mk A Q M D W T E H C P N)
      rw [raabeDuhamelTest_decode_encode_bhist A,
        raabeDuhamelTest_decode_encode_bhist Q,
        raabeDuhamelTest_decode_encode_bhist M,
        raabeDuhamelTest_decode_encode_bhist D,
        raabeDuhamelTest_decode_encode_bhist W,
        raabeDuhamelTest_decode_encode_bhist T,
        raabeDuhamelTest_decode_encode_bhist E,
        raabeDuhamelTest_decode_encode_bhist H,
        raabeDuhamelTest_decode_encode_bhist C,
        raabeDuhamelTest_decode_encode_bhist P,
        raabeDuhamelTest_decode_encode_bhist N]

private theorem RaabeDuhamelTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RaabeDuhamelTestUp} :
    raabeDuhamelTestToEventFlow x = raabeDuhamelTestToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = raabeDuhamelTestFromEventFlow (raabeDuhamelTestToEventFlow x) :=
        (raabeDuhamelTest_round_trip x).symm
      _ = raabeDuhamelTestFromEventFlow (raabeDuhamelTestToEventFlow y) :=
        congrArg raabeDuhamelTestFromEventFlow heq
      _ = some y := raabeDuhamelTest_round_trip y
  exact Option.some.inj optionEq

instance raabeDuhamelTestBHistCarrier : BHistCarrier RaabeDuhamelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := raabeDuhamelTestToEventFlow
  fromEventFlow := raabeDuhamelTestFromEventFlow

instance raabeDuhamelTestChapterTasteGate : ChapterTasteGate RaabeDuhamelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change raabeDuhamelTestFromEventFlow (raabeDuhamelTestToEventFlow x) = some x
    exact raabeDuhamelTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RaabeDuhamelTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RaabeDuhamelTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  raabeDuhamelTestChapterTasteGate

theorem RaabeDuhamelTestTasteGate_single_carrier_alignment :
    (forall h : BHist, raabeDuhamelTestDecodeBHist (raabeDuhamelTestEncodeBHist h) = h) /\
      (forall x : RaabeDuhamelTestUp,
        raabeDuhamelTestFromEventFlow (raabeDuhamelTestToEventFlow x) = some x) /\
        (forall x y : RaabeDuhamelTestUp,
          raabeDuhamelTestToEventFlow x = raabeDuhamelTestToEventFlow y -> x = y) /\
          raabeDuhamelTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨raabeDuhamelTest_decode_encode_bhist,
      raabeDuhamelTest_round_trip,
      (by
        intro x y heq
        exact RaabeDuhamelTestTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RaabeDuhamelTestUp
