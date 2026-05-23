import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularAutomatonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularAutomatonUp : Type where
  | mk :
      (rule initial orbit tag ledger transport routes provenance nameCert : BHist) →
      CellularAutomatonUp
  deriving DecidableEq

def cellularAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularAutomatonEncodeBHist h

def cellularAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularAutomatonDecodeBHist tail)

private theorem cellularAutomatonDecode_encode_bhist :
    ∀ h : BHist,
      cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularAutomatonToEventFlow :
    CellularAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularAutomatonUp.mk rule initial orbit tag ledger transport routes provenance
      nameCert =>
      [[BMark.b0], cellularAutomatonEncodeBHist rule, [BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist initial, [BMark.b1, BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist orbit, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist tag,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularAutomatonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cellularAutomatonEncodeBHist nameCert]

def cellularAutomatonFromEventFlow :
    EventFlow → Option CellularAutomatonUp
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
              | initial :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | orbit :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tag :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
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
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CellularAutomatonUp.mk
                                                                                  (cellularAutomatonDecodeBHist rule)
                                                                                  (cellularAutomatonDecodeBHist initial)
                                                                                  (cellularAutomatonDecodeBHist orbit)
                                                                                  (cellularAutomatonDecodeBHist tag)
                                                                                  (cellularAutomatonDecodeBHist ledger)
                                                                                  (cellularAutomatonDecodeBHist transport)
                                                                                  (cellularAutomatonDecodeBHist routes)
                                                                                  (cellularAutomatonDecodeBHist provenance)
                                                                                  (cellularAutomatonDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem cellularAutomaton_round_trip :
    ∀ x : CellularAutomatonUp,
      cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rule initial orbit tag ledger transport routes provenance nameCert =>
      change
        some
          (CellularAutomatonUp.mk
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist rule))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist initial))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist orbit))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist tag))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist ledger))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist transport))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist routes))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist provenance))
            (cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist nameCert))) =
          some
            (CellularAutomatonUp.mk rule initial orbit tag ledger transport routes
              provenance nameCert)
      rw [cellularAutomatonDecode_encode_bhist rule,
        cellularAutomatonDecode_encode_bhist initial,
        cellularAutomatonDecode_encode_bhist orbit,
        cellularAutomatonDecode_encode_bhist tag,
        cellularAutomatonDecode_encode_bhist ledger,
        cellularAutomatonDecode_encode_bhist transport,
        cellularAutomatonDecode_encode_bhist routes,
        cellularAutomatonDecode_encode_bhist provenance,
        cellularAutomatonDecode_encode_bhist nameCert]

private theorem cellularAutomatonToEventFlow_injective
    {x y : CellularAutomatonUp} :
    cellularAutomatonToEventFlow x = cellularAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow x) =
        cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow y) :=
    congrArg cellularAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularAutomaton_round_trip x).symm
      (Eq.trans hread (cellularAutomaton_round_trip y)))

instance cellularAutomatonBHistCarrier :
    BHistCarrier CellularAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularAutomatonToEventFlow
  fromEventFlow := cellularAutomatonFromEventFlow

instance cellularAutomatonChapterTasteGate :
    ChapterTasteGate CellularAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow x) = some x
    exact cellularAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularAutomatonToEventFlow_injective heq)

instance cellularAutomatonFieldFaithful :
    FieldFaithful CellularAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CellularAutomatonUp.mk rule initial orbit tag ledger transport routes provenance
        nameCert =>
        [rule, initial, orbit, tag, ledger, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk rule₁ initial₁ orbit₁ tag₁ ledger₁ transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk rule₂ initial₂ orbit₂ tag₂ ledger₂ transport₂ routes₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance cellularAutomatonNontrivial :
    Nontrivial CellularAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularAutomatonChapterTasteGate

theorem CellularAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularAutomatonDecodeBHist (cellularAutomatonEncodeBHist h) = h) ∧
      (∀ x : CellularAutomatonUp,
        cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow x) = some x) ∧
        (∀ x y : CellularAutomatonUp,
          cellularAutomatonToEventFlow x = cellularAutomatonToEventFlow y → x = y) ∧
          cellularAutomatonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularAutomatonDecode_encode_bhist
  · constructor
    · exact cellularAutomaton_round_trip
    · constructor
      · intro x y heq
        exact cellularAutomatonToEventFlow_injective heq
      · rfl

theorem CellularAutomatonCarrier_local_rule_exposure (R I O T L H C P N : BHist) :
    ∃ A : CellularAutomatonUp,
      A = CellularAutomatonUp.mk R I O T L H C P N ∧
        cellularAutomatonFromEventFlow (cellularAutomatonToEventFlow A) = some A ∧
          cellularAutomatonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  refine ⟨CellularAutomatonUp.mk R I O T L H C P N, rfl, ?_, rfl⟩
  exact cellularAutomaton_round_trip (CellularAutomatonUp.mk R I O T L H C P N)

end BEDC.Derived.CellularAutomatonUp.TasteGate

namespace BEDC.Derived.CellularAutomatonUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CellularAutomatonUp :=
  TasteGate.taste_gate

end BEDC.Derived.CellularAutomatonUp
