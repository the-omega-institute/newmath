import BEDC.Derived.RealCompletionSelectorSealUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionSelectorSealUp : Type where
  | mk :
      (selectorBudget selectedWindow regSeqReadback limitSeal terminalEndpoint
        transport continuation provenance localName : BHist) →
      RealCompletionSelectorSealUp
  deriving DecidableEq

def realCompletionSelectorSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionSelectorSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionSelectorSealEncodeBHist h

def realCompletionSelectorSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionSelectorSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionSelectorSealDecodeBHist tail)

private theorem realCompletionSelectorSealDecode_encode_bhist :
    ∀ h : BHist,
      realCompletionSelectorSealDecodeBHist (realCompletionSelectorSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem realCompletionSelectorSeal_mk_congr
    {selectorBudget selectorBudget' selectedWindow selectedWindow'
      regSeqReadback regSeqReadback' limitSeal limitSeal'
      terminalEndpoint terminalEndpoint' transport transport'
      continuation continuation' provenance provenance' localName localName' : BHist}
    (hSelectorBudget : selectorBudget' = selectorBudget)
    (hSelectedWindow : selectedWindow' = selectedWindow)
    (hRegSeqReadback : regSeqReadback' = regSeqReadback)
    (hLimitSeal : limitSeal' = limitSeal)
    (hTerminalEndpoint : terminalEndpoint' = terminalEndpoint)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RealCompletionSelectorSealUp.mk selectorBudget' selectedWindow' regSeqReadback'
        limitSeal' terminalEndpoint' transport' continuation' provenance' localName' =
      RealCompletionSelectorSealUp.mk selectorBudget selectedWindow regSeqReadback
        limitSeal terminalEndpoint transport continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSelectorBudget
  cases hSelectedWindow
  cases hRegSeqReadback
  cases hLimitSeal
  cases hTerminalEndpoint
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def realCompletionSelectorSealToEventFlow : RealCompletionSelectorSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionSelectorSealUp.mk selectorBudget selectedWindow regSeqReadback limitSeal
      terminalEndpoint transport continuation provenance localName =>
      [[BMark.b0],
        realCompletionSelectorSealEncodeBHist selectorBudget,
        [BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist selectedWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist regSeqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist terminalEndpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletionSelectorSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist localName]

def realCompletionSelectorSealFromEventFlow : EventFlow → Option RealCompletionSelectorSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selectorBudget :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | selectedWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regSeqReadback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | limitSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | terminalEndpoint :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RealCompletionSelectorSealUp.mk
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    selectorBudget)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    selectedWindow)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    regSeqReadback)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    limitSeal)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    terminalEndpoint)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    transport)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    continuation)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    provenance)
                                                                                  (realCompletionSelectorSealDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem realCompletionSelectorSeal_round_trip :
    ∀ x : RealCompletionSelectorSealUp,
      realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selectorBudget selectedWindow regSeqReadback limitSeal terminalEndpoint transport
      continuation provenance localName =>
      change
        some
          (RealCompletionSelectorSealUp.mk
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist selectorBudget))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist selectedWindow))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist regSeqReadback))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist limitSeal))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist terminalEndpoint))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist transport))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist continuation))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist provenance))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist localName))) =
          some
            (RealCompletionSelectorSealUp.mk selectorBudget selectedWindow regSeqReadback
              limitSeal terminalEndpoint transport continuation provenance localName)
      exact
        congrArg some
          (realCompletionSelectorSeal_mk_congr
            (realCompletionSelectorSealDecode_encode_bhist selectorBudget)
            (realCompletionSelectorSealDecode_encode_bhist selectedWindow)
            (realCompletionSelectorSealDecode_encode_bhist regSeqReadback)
            (realCompletionSelectorSealDecode_encode_bhist limitSeal)
            (realCompletionSelectorSealDecode_encode_bhist terminalEndpoint)
            (realCompletionSelectorSealDecode_encode_bhist transport)
            (realCompletionSelectorSealDecode_encode_bhist continuation)
            (realCompletionSelectorSealDecode_encode_bhist provenance)
            (realCompletionSelectorSealDecode_encode_bhist localName))

private theorem realCompletionSelectorSealToEventFlow_injective
    {x y : RealCompletionSelectorSealUp} :
    realCompletionSelectorSealToEventFlow x = realCompletionSelectorSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
        realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow y) :=
    congrArg realCompletionSelectorSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionSelectorSeal_round_trip x).symm
      (Eq.trans hread (realCompletionSelectorSeal_round_trip y)))

instance realCompletionSelectorSealBHistCarrier : BHistCarrier RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionSelectorSealToEventFlow
  fromEventFlow := realCompletionSelectorSealFromEventFlow

instance realCompletionSelectorSealChapterTasteGate :
    ChapterTasteGate RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
        some x
    exact realCompletionSelectorSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionSelectorSealToEventFlow_injective heq)

instance realCompletionSelectorSealFieldFaithful : FieldFaithful RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealCompletionSelectorSealUp.mk selectorBudget selectedWindow regSeqReadback
        limitSeal terminalEndpoint transport continuation provenance localName =>
        [selectorBudget, selectedWindow, regSeqReadback, limitSeal, terminalEndpoint,
          transport, continuation, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk selectorBudget1 selectedWindow1 regSeqReadback1 limitSeal1 terminalEndpoint1
        transport1 continuation1 provenance1 localName1 =>
        cases y with
        | mk selectorBudget2 selectedWindow2 regSeqReadback2 limitSeal2 terminalEndpoint2
            transport2 continuation2 provenance2 localName2 =>
            injection h with hSelectorBudget t1
            injection t1 with hSelectedWindow t2
            injection t2 with hRegSeqReadback t3
            injection t3 with hLimitSeal t4
            injection t4 with hTerminalEndpoint t5
            injection t5 with hTransport t6
            injection t6 with hContinuation t7
            injection t7 with hProvenance t8
            injection t8 with hLocalName _
            cases hSelectorBudget
            cases hSelectedWindow
            cases hRegSeqReadback
            cases hLimitSeal
            cases hTerminalEndpoint
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

instance realCompletionSelectorSealNontrivial : Nontrivial RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionSelectorSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionSelectorSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletionSelectorSealUp :=
  realCompletionSelectorSealChapterTasteGate

theorem RealCompletionSelectorSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletionSelectorSealDecodeBHist (realCompletionSelectorSealEncodeBHist h) = h) ∧
      (∀ x : RealCompletionSelectorSealUp,
        realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
          some x) ∧
        (∀ x y : RealCompletionSelectorSealUp,
          realCompletionSelectorSealToEventFlow x = realCompletionSelectorSealToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful RealCompletionSelectorSealUp) ∧
            Nonempty (Nontrivial RealCompletionSelectorSealUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact realCompletionSelectorSealDecode_encode_bhist
  · constructor
    · exact realCompletionSelectorSeal_round_trip
    · constructor
      · intro x y heq
        exact realCompletionSelectorSealToEventFlow_injective heq
      · constructor
        · exact ⟨realCompletionSelectorSealFieldFaithful⟩
        · exact ⟨realCompletionSelectorSealNontrivial⟩

end BEDC.Derived.RealCompletionSelectorSealUp
