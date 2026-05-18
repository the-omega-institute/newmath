import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelectorLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

inductive SelectorLedgerUp : Type where
  | mk : (history trace selectors transport cont provenance name : BHist) → SelectorLedgerUp
  deriving DecidableEq

def SelectorLedgerCarrier [AskSetup] [PackageSetup]
    (history trace selectors transport cont provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory history ∧ UnaryHistory trace ∧ UnaryHistory selectors ∧
    UnaryHistory transport ∧ UnaryHistory cont ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont history trace transport ∧ Cont trace selectors cont ∧
        PkgSig bundle provenance pkg

theorem SelectorLedgerNameCertObligations [AskSetup] [PackageSetup]
    {history trace selectors transport cont provenance name route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SelectorLedgerCarrier history trace selectors transport cont provenance name bundle pkg →
      Cont cont name route →
        PkgSig bundle route pkg →
          UnaryHistory history ∧ UnaryHistory trace ∧ UnaryHistory selectors ∧
            UnaryHistory route ∧ Cont history trace transport ∧ Cont trace selectors cont ∧
              Cont cont name route ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont routePkg
  rcases carrier with
    ⟨historyUnary, traceUnary, selectorsUnary, _transportUnary, contUnary,
      _provenanceUnary, nameUnary, historyTrace, traceSelectors, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed contUnary nameUnary routeCont
  exact
    ⟨historyUnary, traceUnary, selectorsUnary, routeUnary, historyTrace, traceSelectors,
      routeCont, provenancePkg, routePkg⟩

theorem SelectorLedgerNoHiddenChoice [AskSetup] [PackageSetup]
    {history trace selectors transport cont provenance name route publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SelectorLedgerCarrier history trace selectors transport cont provenance name bundle pkg →
      Cont cont name route →
        PkgSig bundle route pkg →
          Cont route provenance publicRead →
            UnaryHistory history ∧ UnaryHistory trace ∧ UnaryHistory selectors ∧
              UnaryHistory route ∧ UnaryHistory publicRead ∧ Cont history trace transport ∧
                Cont trace selectors cont ∧ Cont cont name route ∧
                  Cont route provenance publicRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont routePkg publicReadCont
  have obligations :=
    SelectorLedgerNameCertObligations carrier routeCont routePkg
  rcases obligations with
    ⟨historyUnary, traceUnary, selectorsUnary, routeUnary, historyTrace, traceSelectors,
      contNameRoute, provenancePkg, routePkg'⟩
  rcases carrier with
    ⟨_historyUnary, _traceUnary, _selectorsUnary, _transportUnary, _contUnary,
      provenanceUnary, _nameUnary, _historyTrace, _traceSelectors, _provenancePkg⟩
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary publicReadCont
  exact
    ⟨historyUnary, traceUnary, selectorsUnary, routeUnary, publicReadUnary, historyTrace,
      traceSelectors, contNameRoute, publicReadCont, provenancePkg, routePkg'⟩

theorem SelectorLedgerInscriptionEventConsumerRoute [AskSetup] [PackageSetup]
    {history trace selectors transport cont provenance name route publicRead gap
      inscriptionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SelectorLedgerCarrier history trace selectors transport cont provenance name bundle pkg →
      Cont cont name route →
        PkgSig bundle route pkg →
          Cont route provenance publicRead →
            UnaryHistory gap →
              Cont publicRead gap inscriptionRoute →
                UnaryHistory history ∧ UnaryHistory trace ∧ UnaryHistory selectors ∧
                  UnaryHistory route ∧ UnaryHistory publicRead ∧ UnaryHistory inscriptionRoute ∧
                    Cont history trace transport ∧ Cont trace selectors cont ∧
                      Cont cont name route ∧ Cont route provenance publicRead ∧
                        Cont publicRead gap inscriptionRoute ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont routePkg publicReadCont gapUnary inscriptionCont
  have publicRoute :=
    SelectorLedgerNoHiddenChoice carrier routeCont routePkg publicReadCont
  rcases publicRoute with
    ⟨historyUnary, traceUnary, selectorsUnary, routeUnary, publicReadUnary,
      historyTrace, traceSelectors, contNameRoute, routeProvenanceRead, provenancePkg,
      routePkg'⟩
  have inscriptionUnary : UnaryHistory inscriptionRoute :=
    unary_cont_closed publicReadUnary gapUnary inscriptionCont
  exact
    ⟨historyUnary, traceUnary, selectorsUnary, routeUnary, publicReadUnary, inscriptionUnary,
      historyTrace, traceSelectors, contNameRoute, routeProvenanceRead, inscriptionCont,
      provenancePkg, routePkg'⟩

theorem SelectorLedgerCarrier_public_trace_readback [AskSetup] [PackageSetup]
    {history trace selectors transport cont provenance name traceRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SelectorLedgerCarrier history trace selectors transport cont provenance name bundle pkg →
      hsame traceRead trace →
        Cont traceRead selectors selectorRead →
          PkgSig bundle selectorRead pkg →
            UnaryHistory history ∧ UnaryHistory traceRead ∧ UnaryHistory selectors ∧
              UnaryHistory selectorRead ∧ Cont history trace transport ∧
                Cont traceRead selectors selectorRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier sameTrace traceSelectorsRead selectorPkg
  rcases carrier with
    ⟨historyUnary, traceUnary, selectorsUnary, _transportUnary, _contUnary,
      _provenanceUnary, _nameUnary, historyTrace, _traceSelectors, provenancePkg⟩
  have traceReadUnary : UnaryHistory traceRead :=
    unary_transport_symm traceUnary sameTrace
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed traceReadUnary selectorsUnary traceSelectorsRead
  exact
    ⟨historyUnary, traceReadUnary, selectorsUnary, selectorReadUnary, historyTrace,
      traceSelectorsRead, provenancePkg, selectorPkg⟩

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
