import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularRowClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularRowClassifierUp : Type where
  | mk (rule window tags acceptance transport routes provenance nameCert :
      BHist) : CellularRowClassifierUp
  deriving DecidableEq

private def cellularRowClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularRowClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularRowClassifierEncodeBHist h

private def cellularRowClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularRowClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularRowClassifierDecodeBHist tail)

private theorem cellularRowClassifier_decode_encode_bhist :
    ∀ h : BHist,
      cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def cellularRowClassifierToEventFlow : CellularRowClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularRowClassifierUp.mk rule window tags acceptance transport routes provenance
      nameCert =>
      [[BMark.b0],
        cellularRowClassifierEncodeBHist rule,
        [BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist tags,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist acceptance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularRowClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularRowClassifierEncodeBHist nameCert]

private def cellularRowClassifierFromEventFlow : EventFlow → Option CellularRowClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | rule :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | tags :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | acceptance :: rest7 =>
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
                                              | routes :: rest11 =>
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
                                                                        (CellularRowClassifierUp.mk
                                                                          (cellularRowClassifierDecodeBHist
                                                                            rule)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            window)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            tags)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            acceptance)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            transport)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            routes)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            provenance)
                                                                          (cellularRowClassifierDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem cellularRowClassifier_round_trip :
    ∀ x : CellularRowClassifierUp,
      cellularRowClassifierFromEventFlow (cellularRowClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rule window tags acceptance transport routes provenance nameCert =>
      change
        some
          (CellularRowClassifierUp.mk
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist rule))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist window))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist tags))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist acceptance))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist transport))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist routes))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist provenance))
            (cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist nameCert))) =
          some
            (CellularRowClassifierUp.mk rule window tags acceptance transport routes provenance
              nameCert)
      rw [cellularRowClassifier_decode_encode_bhist rule,
        cellularRowClassifier_decode_encode_bhist window,
        cellularRowClassifier_decode_encode_bhist tags,
        cellularRowClassifier_decode_encode_bhist acceptance,
        cellularRowClassifier_decode_encode_bhist transport,
        cellularRowClassifier_decode_encode_bhist routes,
        cellularRowClassifier_decode_encode_bhist provenance,
        cellularRowClassifier_decode_encode_bhist nameCert]

private theorem cellularRowClassifierToEventFlow_injective {x y : CellularRowClassifierUp} :
    cellularRowClassifierToEventFlow x = cellularRowClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularRowClassifierFromEventFlow (cellularRowClassifierToEventFlow x) =
        cellularRowClassifierFromEventFlow (cellularRowClassifierToEventFlow y) :=
    congrArg cellularRowClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularRowClassifier_round_trip x).symm
      (Eq.trans hread (cellularRowClassifier_round_trip y)))

private def cellularRowClassifierFields :
    CellularRowClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularRowClassifierUp.mk rule window tags acceptance transport routes provenance
      nameCert =>
      [rule, window, tags, acceptance, transport, routes, provenance, nameCert]

private theorem cellularRowClassifier_field_faithful :
    ∀ x y : CellularRowClassifierUp,
      cellularRowClassifierFields x = cellularRowClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk rule window tags acceptance transport routes provenance nameCert =>
      cases y with
      | mk rule' window' tags' acceptance' transport' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance cellularRowClassifierBHistCarrier :
    BHistCarrier CellularRowClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularRowClassifierToEventFlow
  fromEventFlow := cellularRowClassifierFromEventFlow

instance cellularRowClassifierChapterTasteGate :
    ChapterTasteGate CellularRowClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularRowClassifierFromEventFlow
        (cellularRowClassifierToEventFlow x) = some x
    exact cellularRowClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularRowClassifierToEventFlow_injective heq)

instance cellularRowClassifierFieldFaithful :
    FieldFaithful CellularRowClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularRowClassifierFields
  field_faithful := cellularRowClassifier_field_faithful

instance cellularRowClassifierNontrivial :
    Nontrivial CellularRowClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularRowClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularRowClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularRowClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularRowClassifierChapterTasteGate

theorem CellularRowClassifierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CellularRowClassifierUp) ∧
      Nonempty (FieldFaithful CellularRowClassifierUp) ∧
      Nonempty (Nontrivial CellularRowClassifierUp) ∧
        (∀ h : BHist,
          cellularRowClassifierDecodeBHist (cellularRowClassifierEncodeBHist h) = h) ∧
          cellularRowClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨cellularRowClassifierChapterTasteGate⟩, ⟨cellularRowClassifierFieldFaithful⟩,
      ⟨cellularRowClassifierNontrivial⟩, cellularRowClassifier_decode_encode_bhist, rfl⟩

end BEDC.Derived.CellularRowClassifierUp
