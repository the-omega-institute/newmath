import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticFixedPointUp : Type where
  | mk
      (socketFamily farEnd inscription ledger transport continuation provenance nameCert : BHist) :
      ApophaticFixedPointUp
  deriving DecidableEq

def apophaticFixedPointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticFixedPointEncodeBHist h

def apophaticFixedPointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticFixedPointDecodeBHist tail)

private theorem apophaticFixedPointDecode_encode_bhist :
    forall h : BHist,
      apophaticFixedPointDecodeBHist (apophaticFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apophaticFixedPointToEventFlow : ApophaticFixedPointUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticFixedPointUp.mk socketFamily farEnd inscription ledger transport continuation
      provenance nameCert =>
      [[BMark.b0],
        apophaticFixedPointEncodeBHist socketFamily,
        [BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist farEnd,
        [BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        apophaticFixedPointEncodeBHist nameCert]

def apophaticFixedPointFromEventFlow : EventFlow -> Option ApophaticFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socketFamily :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | farEnd :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | inscription :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ApophaticFixedPointUp.mk
                                                                          (apophaticFixedPointDecodeBHist
                                                                            socketFamily)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            farEnd)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            inscription)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            ledger)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            transport)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            continuation)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            provenance)
                                                                          (apophaticFixedPointDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem apophaticFixedPoint_round_trip :
    forall x : ApophaticFixedPointUp,
      apophaticFixedPointFromEventFlow (apophaticFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socketFamily farEnd inscription ledger transport continuation provenance nameCert =>
      change
        some
            (ApophaticFixedPointUp.mk
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist socketFamily))
              (apophaticFixedPointDecodeBHist (apophaticFixedPointEncodeBHist farEnd))
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist inscription))
              (apophaticFixedPointDecodeBHist (apophaticFixedPointEncodeBHist ledger))
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist transport))
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist continuation))
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist provenance))
              (apophaticFixedPointDecodeBHist
                (apophaticFixedPointEncodeBHist nameCert))) =
          some
            (ApophaticFixedPointUp.mk socketFamily farEnd inscription ledger transport
              continuation provenance nameCert)
      rw [apophaticFixedPointDecode_encode_bhist socketFamily,
        apophaticFixedPointDecode_encode_bhist farEnd,
        apophaticFixedPointDecode_encode_bhist inscription,
        apophaticFixedPointDecode_encode_bhist ledger,
        apophaticFixedPointDecode_encode_bhist transport,
        apophaticFixedPointDecode_encode_bhist continuation,
        apophaticFixedPointDecode_encode_bhist provenance,
        apophaticFixedPointDecode_encode_bhist nameCert]

theorem apophaticFixedPointToEventFlow_injective {x y : ApophaticFixedPointUp} :
    apophaticFixedPointToEventFlow x = apophaticFixedPointToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apophaticFixedPointFromEventFlow (apophaticFixedPointToEventFlow x) =
        apophaticFixedPointFromEventFlow (apophaticFixedPointToEventFlow y) :=
    congrArg apophaticFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticFixedPoint_round_trip x).symm
      (Eq.trans hread (apophaticFixedPoint_round_trip y)))

def apophaticFixedPointFields : ApophaticFixedPointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticFixedPointUp.mk socketFamily farEnd inscription ledger transport continuation
      provenance nameCert =>
      [socketFamily, farEnd, inscription, ledger, transport, continuation, provenance,
        nameCert]

private theorem apophaticFixedPoint_field_faithful :
    forall x y : ApophaticFixedPointUp,
      apophaticFixedPointFields x = apophaticFixedPointFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk socketFamily1 farEnd1 inscription1 ledger1 transport1 continuation1 provenance1
      nameCert1 =>
      cases y with
      | mk socketFamily2 farEnd2 inscription2 ledger2 transport2 continuation2 provenance2
          nameCert2 =>
          cases h
          rfl

instance apophaticFixedPointBHistCarrier : BHistCarrier ApophaticFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apophaticFixedPointToEventFlow
  fromEventFlow := apophaticFixedPointFromEventFlow

instance apophaticFixedPointChapterTasteGate : ChapterTasteGate ApophaticFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apophaticFixedPointFromEventFlow (apophaticFixedPointToEventFlow x) = some x
    exact apophaticFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticFixedPointToEventFlow_injective heq)

instance apophaticFixedPointFieldFaithful : FieldFaithful ApophaticFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apophaticFixedPointFields
  field_faithful := apophaticFixedPoint_field_faithful

instance apophaticFixedPointNontrivial : Nontrivial ApophaticFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApophaticFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ApophaticFixedPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApophaticFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apophaticFixedPointChapterTasteGate

theorem ApophaticFixedPointTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ApophaticFixedPointUp) ∧
      Nonempty (FieldFaithful ApophaticFixedPointUp) ∧
        Nonempty (Nontrivial ApophaticFixedPointUp) ∧
          (forall h : BHist,
            apophaticFixedPointDecodeBHist (apophaticFixedPointEncodeBHist h) = h) ∧
            (forall x : ApophaticFixedPointUp,
              apophaticFixedPointFromEventFlow (apophaticFixedPointToEventFlow x) =
                some x) ∧
              (forall x y : ApophaticFixedPointUp,
                apophaticFixedPointToEventFlow x = apophaticFixedPointToEventFlow y ->
                  x = y) ∧
                apophaticFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨apophaticFixedPointChapterTasteGate⟩
  · constructor
    · exact ⟨apophaticFixedPointFieldFaithful⟩
    · constructor
      · exact ⟨apophaticFixedPointNontrivial⟩
      · constructor
        · exact apophaticFixedPointDecode_encode_bhist
        · constructor
          · exact apophaticFixedPoint_round_trip
          · constructor
            · intro x y heq
              exact apophaticFixedPointToEventFlow_injective heq
            · rfl

end BEDC.Derived.ApophaticFixedPointUp
