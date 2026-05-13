import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularOrbitSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularOrbitSubstrateUp : Type where
  | mk : (rule initial window localLedger transport continuation provenance name : BHist) →
      CellularOrbitSubstrateUp
  deriving DecidableEq

def cellularOrbitSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularOrbitSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularOrbitSubstrateEncodeBHist h

def cellularOrbitSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularOrbitSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularOrbitSubstrateDecodeBHist tail)

private theorem cellularOrbitSubstrateDecode_encode_bhist :
    ∀ h : BHist, cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cellularOrbitSubstrate_mk_congr
    {rule rule' initial initial' window window' localLedger localLedger' transport transport'
      continuation continuation' provenance provenance' name name' : BHist}
    (hRule : rule' = rule)
    (hInitial : initial' = initial)
    (hWindow : window' = window)
    (hLocalLedger : localLedger' = localLedger)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CellularOrbitSubstrateUp.mk rule' initial' window' localLedger' transport' continuation'
        provenance' name' =
      CellularOrbitSubstrateUp.mk rule initial window localLedger transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRule
  cases hInitial
  cases hWindow
  cases hLocalLedger
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def cellularOrbitSubstrateToEventFlow : CellularOrbitSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularOrbitSubstrateUp.mk rule initial window localLedger transport continuation provenance name =>
      [[BMark.b0],
        cellularOrbitSubstrateEncodeBHist rule,
        [BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist initial,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist localLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularOrbitSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularOrbitSubstrateEncodeBHist name]

def cellularOrbitSubstrateFromEventFlow : EventFlow → Option CellularOrbitSubstrateUp
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
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localLedger :: rest7 =>
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
                                                                        (CellularOrbitSubstrateUp.mk
                                                                          (cellularOrbitSubstrateDecodeBHist rule)
                                                                          (cellularOrbitSubstrateDecodeBHist initial)
                                                                          (cellularOrbitSubstrateDecodeBHist window)
                                                                          (cellularOrbitSubstrateDecodeBHist localLedger)
                                                                          (cellularOrbitSubstrateDecodeBHist transport)
                                                                          (cellularOrbitSubstrateDecodeBHist continuation)
                                                                          (cellularOrbitSubstrateDecodeBHist provenance)
                                                                          (cellularOrbitSubstrateDecodeBHist name))
                                                                  | _ :: _ => none

private theorem cellularOrbitSubstrate_round_trip :
    ∀ x : CellularOrbitSubstrateUp,
      cellularOrbitSubstrateFromEventFlow (cellularOrbitSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rule initial window localLedger transport continuation provenance name =>
      change
        some
          (CellularOrbitSubstrateUp.mk
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist rule))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist initial))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist window))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist localLedger))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist transport))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist continuation))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist provenance))
            (cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist name))) =
          some
            (CellularOrbitSubstrateUp.mk rule initial window localLedger transport continuation
              provenance name)
      exact
        congrArg some
          (cellularOrbitSubstrate_mk_congr
            (cellularOrbitSubstrateDecode_encode_bhist rule)
            (cellularOrbitSubstrateDecode_encode_bhist initial)
            (cellularOrbitSubstrateDecode_encode_bhist window)
            (cellularOrbitSubstrateDecode_encode_bhist localLedger)
            (cellularOrbitSubstrateDecode_encode_bhist transport)
            (cellularOrbitSubstrateDecode_encode_bhist continuation)
            (cellularOrbitSubstrateDecode_encode_bhist provenance)
            (cellularOrbitSubstrateDecode_encode_bhist name))

private theorem cellularOrbitSubstrateToEventFlow_injective {x y : CellularOrbitSubstrateUp} :
    cellularOrbitSubstrateToEventFlow x = cellularOrbitSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularOrbitSubstrateFromEventFlow (cellularOrbitSubstrateToEventFlow x) =
        cellularOrbitSubstrateFromEventFlow (cellularOrbitSubstrateToEventFlow y) :=
    congrArg cellularOrbitSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularOrbitSubstrate_round_trip x).symm
      (Eq.trans hread (cellularOrbitSubstrate_round_trip y)))

instance cellularOrbitSubstrateBHistCarrier : BHistCarrier CellularOrbitSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularOrbitSubstrateToEventFlow
  fromEventFlow := cellularOrbitSubstrateFromEventFlow

instance cellularOrbitSubstrateChapterTasteGate :
    ChapterTasteGate CellularOrbitSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularOrbitSubstrateFromEventFlow (cellularOrbitSubstrateToEventFlow x) = some x
    exact cellularOrbitSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularOrbitSubstrateToEventFlow_injective heq)

instance cellularOrbitSubstrateFieldFaithful : FieldFaithful CellularOrbitSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CellularOrbitSubstrateUp.mk rule initial window localLedger transport continuation provenance name =>
        [rule, initial, window, localLedger, transport, continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk rule1 initial1 window1 localLedger1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk rule2 initial2 window2 localLedger2 transport2 continuation2 provenance2 name2 =>
            injection h with hRule t1
            injection t1 with hInitial t2
            injection t2 with hWindow t3
            injection t3 with hLocal t4
            injection t4 with hTransport t5
            injection t5 with hContinuation t6
            injection t6 with hProvenance t7
            injection t7 with hName _
            cases hRule
            cases hInitial
            cases hWindow
            cases hLocal
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

instance cellularOrbitSubstrateNontrivial : Nontrivial CellularOrbitSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularOrbitSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularOrbitSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CellularOrbitSubstrateTasteGate_single_carrier_alignment :
    (forall h : BHist,
        cellularOrbitSubstrateDecodeBHist (cellularOrbitSubstrateEncodeBHist h) = h) /\
      (forall x : CellularOrbitSubstrateUp,
        cellularOrbitSubstrateFromEventFlow (cellularOrbitSubstrateToEventFlow x) = some x) /\
      (forall x y : CellularOrbitSubstrateUp,
        cellularOrbitSubstrateToEventFlow x = cellularOrbitSubstrateToEventFlow y -> x = y) /\
      cellularOrbitSubstrateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularOrbitSubstrateDecode_encode_bhist
  · constructor
    · exact cellularOrbitSubstrate_round_trip
    · constructor
      · intro x y heq
        exact cellularOrbitSubstrateToEventFlow_injective heq
      · rfl

end BEDC.Derived.CellularOrbitSubstrateUp
