import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularLocalUpdateRuleUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularLocalUpdateRuleUp : Type where
  | mk (state width neighbourhood ruleRow nextState transports routes provenance nameCert :
      BHist) : CellularLocalUpdateRuleUp
  deriving DecidableEq

private def cellularLocalUpdateRuleEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularLocalUpdateRuleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularLocalUpdateRuleEncodeBHist h

private def cellularLocalUpdateRuleDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularLocalUpdateRuleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularLocalUpdateRuleDecodeBHist tail)

private theorem cellularLocalUpdateRule_decode_encode_bhist :
    ∀ h : BHist,
      cellularLocalUpdateRuleDecodeBHist (cellularLocalUpdateRuleEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def cellularLocalUpdateRuleToEventFlow :
    CellularLocalUpdateRuleUp → EventFlow
  | CellularLocalUpdateRuleUp.mk state width neighbourhood ruleRow nextState transports
      routes provenance nameCert =>
      [[BMark.b0],
        cellularLocalUpdateRuleEncodeBHist state,
        [BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist width,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist neighbourhood,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist ruleRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist nextState,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularLocalUpdateRuleEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cellularLocalUpdateRuleEncodeBHist nameCert]

private def cellularLocalUpdateRuleFromEventFlow :
    EventFlow → Option CellularLocalUpdateRuleUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | state :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | width :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | neighbourhood :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ruleRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nextState :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (CellularLocalUpdateRuleUp.mk
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    state)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    width)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    neighbourhood)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    ruleRow)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    nextState)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    transports)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    routes)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    provenance)
                                                                                  (cellularLocalUpdateRuleDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem cellularLocalUpdateRule_round_trip :
    ∀ x : CellularLocalUpdateRuleUp,
      cellularLocalUpdateRuleFromEventFlow (cellularLocalUpdateRuleToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk state width neighbourhood ruleRow nextState transports routes provenance nameCert =>
      change
        some
          (CellularLocalUpdateRuleUp.mk
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist state))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist width))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist neighbourhood))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist ruleRow))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist nextState))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist transports))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist routes))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist provenance))
            (cellularLocalUpdateRuleDecodeBHist
              (cellularLocalUpdateRuleEncodeBHist nameCert))) =
          some
            (CellularLocalUpdateRuleUp.mk state width neighbourhood ruleRow nextState
              transports routes provenance nameCert)
      rw [cellularLocalUpdateRule_decode_encode_bhist state,
        cellularLocalUpdateRule_decode_encode_bhist width,
        cellularLocalUpdateRule_decode_encode_bhist neighbourhood,
        cellularLocalUpdateRule_decode_encode_bhist ruleRow,
        cellularLocalUpdateRule_decode_encode_bhist nextState,
        cellularLocalUpdateRule_decode_encode_bhist transports,
        cellularLocalUpdateRule_decode_encode_bhist routes,
        cellularLocalUpdateRule_decode_encode_bhist provenance,
        cellularLocalUpdateRule_decode_encode_bhist nameCert]

private theorem cellularLocalUpdateRuleToEventFlow_injective
    {x y : CellularLocalUpdateRuleUp} :
    cellularLocalUpdateRuleToEventFlow x = cellularLocalUpdateRuleToEventFlow y → x = y := by
  intro heq
  have hread :
      cellularLocalUpdateRuleFromEventFlow (cellularLocalUpdateRuleToEventFlow x) =
        cellularLocalUpdateRuleFromEventFlow (cellularLocalUpdateRuleToEventFlow y) :=
    congrArg cellularLocalUpdateRuleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularLocalUpdateRule_round_trip x).symm
      (Eq.trans hread (cellularLocalUpdateRule_round_trip y)))

private def cellularLocalUpdateRuleFields :
    CellularLocalUpdateRuleUp → List BHist
  | CellularLocalUpdateRuleUp.mk state width neighbourhood ruleRow nextState transports
      routes provenance nameCert =>
      [state, width, neighbourhood, ruleRow, nextState, transports, routes, provenance,
        nameCert]

private theorem cellularLocalUpdateRule_field_faithful :
    ∀ x y : CellularLocalUpdateRuleUp,
      cellularLocalUpdateRuleFields x = cellularLocalUpdateRuleFields y → x = y := by
  intro x y hfields
  cases x with
  | mk state width neighbourhood ruleRow nextState transports routes provenance nameCert =>
      cases y with
      | mk state' width' neighbourhood' ruleRow' nextState' transports' routes' provenance'
          nameCert' =>
          cases hfields
          rfl

instance cellularLocalUpdateRuleBHistCarrier :
    BHistCarrier CellularLocalUpdateRuleUp where
  toEventFlow := cellularLocalUpdateRuleToEventFlow
  fromEventFlow := cellularLocalUpdateRuleFromEventFlow

instance cellularLocalUpdateRuleChapterTasteGate :
    ChapterTasteGate CellularLocalUpdateRuleUp where
  round_trip := by
    intro x
    change
      cellularLocalUpdateRuleFromEventFlow
        (cellularLocalUpdateRuleToEventFlow x) = some x
    exact cellularLocalUpdateRule_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularLocalUpdateRuleToEventFlow_injective heq)

instance cellularLocalUpdateRuleFieldFaithful :
    FieldFaithful CellularLocalUpdateRuleUp where
  fields := cellularLocalUpdateRuleFields
  field_faithful := cellularLocalUpdateRule_field_faithful

instance cellularLocalUpdateRuleNontrivial :
    Nontrivial CellularLocalUpdateRuleUp where
  witness_pair :=
    ⟨CellularLocalUpdateRuleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularLocalUpdateRuleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularLocalUpdateRuleUp :=
  cellularLocalUpdateRuleChapterTasteGate

theorem CellularLocalUpdateRuleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CellularLocalUpdateRuleUp) ∧
      Nonempty (FieldFaithful CellularLocalUpdateRuleUp) ∧
      Nonempty (Nontrivial CellularLocalUpdateRuleUp) ∧
        (∀ h : BHist,
          cellularLocalUpdateRuleDecodeBHist (cellularLocalUpdateRuleEncodeBHist h) = h) ∧
          cellularLocalUpdateRuleEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨⟨cellularLocalUpdateRuleChapterTasteGate⟩,
      ⟨cellularLocalUpdateRuleFieldFaithful⟩,
      ⟨cellularLocalUpdateRuleNontrivial⟩,
      cellularLocalUpdateRule_decode_encode_bhist, rfl⟩

end BEDC.Derived.CellularLocalUpdateRuleUp.TasteGate

namespace BEDC.Derived.CellularLocalUpdateRuleUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CellularLocalUpdateRuleUp :=
  TasteGate.taste_gate

end BEDC.Derived.CellularLocalUpdateRuleUp
