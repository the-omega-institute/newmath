import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelectorLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive SelectorLedgerUp : Type where
  | mk : (history trace selectors transport cont provenance name : BHist) → SelectorLedgerUp
  deriving DecidableEq

def selectorLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: selectorLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: selectorLedgerEncodeBHist h

def selectorLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (selectorLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (selectorLedgerDecodeBHist tail)

private theorem selectorLedgerDecode_encode_bhist :
    ∀ h : BHist, selectorLedgerDecodeBHist (selectorLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem SelectorLedgerTasteGate_single_carrier_alignment_mk_congr
    {history history' trace trace' selectors selectors' transport transport' cont cont'
      provenance provenance' name name' : BHist}
    (hHistory : history' = history)
    (hTrace : trace' = trace)
    (hSelectors : selectors' = selectors)
    (hTransport : transport' = transport)
    (hCont : cont' = cont)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    SelectorLedgerUp.mk history' trace' selectors' transport' cont' provenance' name' =
      SelectorLedgerUp.mk history trace selectors transport cont provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hHistory
  cases hTrace
  cases hSelectors
  cases hTransport
  cases hCont
  cases hProvenance
  cases hName
  rfl

def selectorLedgerToEventFlow : SelectorLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SelectorLedgerUp.mk history trace selectors transport cont provenance name =>
      [[BMark.b0],
        selectorLedgerEncodeBHist history,
        [BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist selectors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectorLedgerEncodeBHist name]

def selectorLedgerFromEventFlow : EventFlow → Option SelectorLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectors :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | cont :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (SelectorLedgerUp.mk
                                                                  (selectorLedgerDecodeBHist
                                                                    history)
                                                                  (selectorLedgerDecodeBHist
                                                                    trace)
                                                                  (selectorLedgerDecodeBHist
                                                                    selectors)
                                                                  (selectorLedgerDecodeBHist
                                                                    transport)
                                                                  (selectorLedgerDecodeBHist
                                                                    cont)
                                                                  (selectorLedgerDecodeBHist
                                                                    provenance)
                                                                  (selectorLedgerDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem selectorLedger_round_trip :
    ∀ x : SelectorLedgerUp,
      selectorLedgerFromEventFlow (selectorLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history trace selectors transport cont provenance name =>
      change
        some
          (SelectorLedgerUp.mk
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist history))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist trace))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist selectors))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist transport))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist cont))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist provenance))
            (selectorLedgerDecodeBHist (selectorLedgerEncodeBHist name))) =
          some
            (SelectorLedgerUp.mk history trace selectors transport cont provenance name)
      exact
        congrArg some
          (SelectorLedgerTasteGate_single_carrier_alignment_mk_congr
            (selectorLedgerDecode_encode_bhist history)
            (selectorLedgerDecode_encode_bhist trace)
            (selectorLedgerDecode_encode_bhist selectors)
            (selectorLedgerDecode_encode_bhist transport)
            (selectorLedgerDecode_encode_bhist cont)
            (selectorLedgerDecode_encode_bhist provenance)
            (selectorLedgerDecode_encode_bhist name))

private theorem selectorLedgerToEventFlow_injective {x y : SelectorLedgerUp} :
    selectorLedgerToEventFlow x = selectorLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      selectorLedgerFromEventFlow (selectorLedgerToEventFlow x) =
        selectorLedgerFromEventFlow (selectorLedgerToEventFlow y) :=
    congrArg selectorLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (selectorLedger_round_trip x).symm
      (Eq.trans hread (selectorLedger_round_trip y)))

theorem SelectorLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist, selectorLedgerDecodeBHist (selectorLedgerEncodeBHist h) = h) /\
      (forall x : SelectorLedgerUp,
        selectorLedgerFromEventFlow (selectorLedgerToEventFlow x) = some x) /\
        (forall x y : SelectorLedgerUp,
          selectorLedgerToEventFlow x = selectorLedgerToEventFlow y -> x = y) /\
          selectorLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact selectorLedgerDecode_encode_bhist
  · constructor
    · exact selectorLedger_round_trip
    · constructor
      · intro x y heq
        exact selectorLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.SelectorLedgerUp
