import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CozeroSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CozeroSetUp : Type where
  | mk (continuousMap realObservation apartness openRow setMembership transport replay
      provenance name : BHist) : CozeroSetUp
  deriving DecidableEq

def cozeroSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cozeroSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cozeroSetEncodeBHist h

def cozeroSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cozeroSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cozeroSetDecodeBHist tail)

private theorem cozeroSetDecode_encode_bhist :
    ∀ h : BHist, cozeroSetDecodeBHist (cozeroSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cozeroSetToEventFlow : CozeroSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CozeroSetUp.mk continuousMap realObservation apartness openRow setMembership transport replay
      provenance name =>
      [cozeroSetEncodeBHist continuousMap,
        cozeroSetEncodeBHist realObservation,
        cozeroSetEncodeBHist apartness,
        cozeroSetEncodeBHist openRow,
        cozeroSetEncodeBHist setMembership,
        cozeroSetEncodeBHist transport,
        cozeroSetEncodeBHist replay,
        cozeroSetEncodeBHist provenance,
        cozeroSetEncodeBHist name]

def cozeroSetFromEventFlow : EventFlow → Option CozeroSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | continuousMap :: rest0 =>
      match rest0 with
      | [] => none
      | realObservation :: rest1 =>
          match rest1 with
          | [] => none
          | apartness :: rest2 =>
              match rest2 with
              | [] => none
              | openRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | setMembership :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CozeroSetUp.mk
                                              (cozeroSetDecodeBHist continuousMap)
                                              (cozeroSetDecodeBHist realObservation)
                                              (cozeroSetDecodeBHist apartness)
                                              (cozeroSetDecodeBHist openRow)
                                              (cozeroSetDecodeBHist setMembership)
                                              (cozeroSetDecodeBHist transport)
                                              (cozeroSetDecodeBHist replay)
                                              (cozeroSetDecodeBHist provenance)
                                              (cozeroSetDecodeBHist name))
                                      | _ :: _ => none

private theorem cozeroSet_round_trip :
    ∀ x : CozeroSetUp, cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk continuousMap realObservation apartness openRow setMembership transport replay provenance
      name =>
      change
        some
          (CozeroSetUp.mk
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist continuousMap))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist realObservation))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist apartness))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist openRow))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist setMembership))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist transport))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist replay))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist provenance))
            (cozeroSetDecodeBHist (cozeroSetEncodeBHist name))) =
          some
            (CozeroSetUp.mk continuousMap realObservation apartness openRow setMembership
              transport replay provenance name)
      rw [cozeroSetDecode_encode_bhist continuousMap,
        cozeroSetDecode_encode_bhist realObservation,
        cozeroSetDecode_encode_bhist apartness,
        cozeroSetDecode_encode_bhist openRow,
        cozeroSetDecode_encode_bhist setMembership,
        cozeroSetDecode_encode_bhist transport,
        cozeroSetDecode_encode_bhist replay,
        cozeroSetDecode_encode_bhist provenance,
        cozeroSetDecode_encode_bhist name]

private theorem CozeroSetToEventFlow_injective {x y : CozeroSetUp} :
    cozeroSetToEventFlow x = cozeroSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cozeroSetFromEventFlow (cozeroSetToEventFlow x) =
        cozeroSetFromEventFlow (cozeroSetToEventFlow y) :=
    congrArg cozeroSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cozeroSet_round_trip x).symm (Eq.trans hread (cozeroSet_round_trip y)))

instance cozeroSetBHistCarrier : BHistCarrier CozeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cozeroSetToEventFlow
  fromEventFlow := cozeroSetFromEventFlow

instance cozeroSetChapterTasteGate : ChapterTasteGate CozeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x
    exact cozeroSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CozeroSetToEventFlow_injective heq)

instance cozeroSetNontrivial : Nontrivial CozeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CozeroSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CozeroSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CozeroSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cozeroSetChapterTasteGate

theorem CozeroSetTasteGate_single_carrier_alignment :
    (forall h : BHist, cozeroSetDecodeBHist (cozeroSetEncodeBHist h) = h) /\
      (forall x : CozeroSetUp, cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x) /\
      (forall x y : CozeroSetUp, cozeroSetToEventFlow x = cozeroSetToEventFlow y -> x = y) /\
      cozeroSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cozeroSetDecode_encode_bhist
  · constructor
    · exact cozeroSet_round_trip
    · constructor
      · intro x y h
        exact CozeroSetToEventFlow_injective h
      · rfl

end BEDC.Derived.CozeroSetUp
