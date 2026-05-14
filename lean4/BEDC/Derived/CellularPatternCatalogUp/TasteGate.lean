import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularPatternCatalogUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularPatternCatalogUp : Type where
  | mk (rule window tag catalog transport route provenance name : BHist) :
      CellularPatternCatalogUp
  deriving DecidableEq

def cellularPatternCatalogEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularPatternCatalogEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularPatternCatalogEncodeBHist h

def cellularPatternCatalogDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularPatternCatalogDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularPatternCatalogDecodeBHist tail)

private theorem cellularPatternCatalog_decode_encode_bhist :
    ∀ h : BHist,
      cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cellularPatternCatalogToEventFlow : CellularPatternCatalogUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularPatternCatalogUp.mk rule window tag catalog transport route provenance name =>
      [[BMark.b0],
        cellularPatternCatalogEncodeBHist rule,
        [BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist tag,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist catalog,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularPatternCatalogEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularPatternCatalogEncodeBHist name]

def cellularPatternCatalogFromEventFlow : EventFlow → Option CellularPatternCatalogUp
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
                      | tag :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | catalog :: rest7 =>
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
                                              | route :: rest11 =>
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
                                                                        (CellularPatternCatalogUp.mk
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            rule)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            window)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            tag)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            catalog)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            transport)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            route)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            provenance)
                                                                          (cellularPatternCatalogDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem cellularPatternCatalog_round_trip :
    ∀ x : CellularPatternCatalogUp,
      cellularPatternCatalogFromEventFlow (cellularPatternCatalogToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rule window tag catalog transport route provenance name =>
      change
        some
          (CellularPatternCatalogUp.mk
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist rule))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist window))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist tag))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist catalog))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist transport))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist route))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist provenance))
            (cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist name))) =
          some
            (CellularPatternCatalogUp.mk rule window tag catalog transport route provenance
              name)
      rw [cellularPatternCatalog_decode_encode_bhist rule,
        cellularPatternCatalog_decode_encode_bhist window,
        cellularPatternCatalog_decode_encode_bhist tag,
        cellularPatternCatalog_decode_encode_bhist catalog,
        cellularPatternCatalog_decode_encode_bhist transport,
        cellularPatternCatalog_decode_encode_bhist route,
        cellularPatternCatalog_decode_encode_bhist provenance,
        cellularPatternCatalog_decode_encode_bhist name]

private theorem cellularPatternCatalogToEventFlow_injective
    {x y : CellularPatternCatalogUp} :
    cellularPatternCatalogToEventFlow x = cellularPatternCatalogToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularPatternCatalogFromEventFlow (cellularPatternCatalogToEventFlow x) =
        cellularPatternCatalogFromEventFlow (cellularPatternCatalogToEventFlow y) :=
    congrArg cellularPatternCatalogFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularPatternCatalog_round_trip x).symm
      (Eq.trans hread (cellularPatternCatalog_round_trip y)))

instance cellularPatternCatalogBHistCarrier : BHistCarrier CellularPatternCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularPatternCatalogToEventFlow
  fromEventFlow := cellularPatternCatalogFromEventFlow

instance cellularPatternCatalogChapterTasteGate :
    ChapterTasteGate CellularPatternCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularPatternCatalogFromEventFlow (cellularPatternCatalogToEventFlow x) = some x
    exact cellularPatternCatalog_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularPatternCatalogToEventFlow_injective heq)

instance cellularPatternCatalogFieldFaithful : FieldFaithful CellularPatternCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CellularPatternCatalogUp.mk rule window tag catalog transport route provenance name =>
        [rule, window, tag, catalog, transport, route, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk rule window tag catalog transport route provenance name =>
        cases y with
        | mk rule' window' tag' catalog' transport' route' provenance' name' =>
            cases hfields
            rfl

instance cellularPatternCatalogNontrivial : Nontrivial CellularPatternCatalogUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨CellularPatternCatalogUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularPatternCatalogUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularPatternCatalogUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem CellularPatternCatalogTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularPatternCatalogDecodeBHist (cellularPatternCatalogEncodeBHist h) = h) ∧
      (∀ x : CellularPatternCatalogUp,
        cellularPatternCatalogFromEventFlow (cellularPatternCatalogToEventFlow x) = some x) ∧
        (∀ x y : CellularPatternCatalogUp,
          cellularPatternCatalogToEventFlow x = cellularPatternCatalogToEventFlow y → x = y) ∧
          cellularPatternCatalogEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularPatternCatalog_decode_encode_bhist
  · constructor
    · exact cellularPatternCatalog_round_trip
    · constructor
      · intro x y heq
        exact cellularPatternCatalogToEventFlow_injective heq
      · rfl

end BEDC.Derived.CellularPatternCatalogUp
