import BEDC.Derived.BoundedLinearOperatorUp.TasteGate

namespace BEDC.Derived.BoundedLinearOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedLinearOperatorCarrier_composition_closure [AskSetup] [PackageSetup]
    {source middle target firstEndpoint firstBound firstLedger firstTransport
      firstContinuation firstProvenance firstName secondEndpoint secondBound secondLedger
      secondTransport secondContinuation secondProvenance secondName compositeEndpoint
      compositeBound compositeLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedLinearOperatorCarrier source middle firstEndpoint firstBound firstLedger
        firstTransport firstContinuation firstProvenance firstName bundle pkg ->
      BoundedLinearOperatorCarrier middle target secondEndpoint secondBound secondLedger
        secondTransport secondContinuation secondProvenance secondName bundle pkg ->
        Cont firstEndpoint secondEndpoint compositeEndpoint ->
          Cont firstBound secondBound compositeBound ->
            Cont firstLedger secondLedger compositeLedger ->
              PkgSig bundle compositeLedger pkg ->
                UnaryHistory compositeEndpoint ∧ UnaryHistory compositeBound ∧
                  UnaryHistory compositeLedger ∧
                    Cont firstEndpoint secondEndpoint compositeEndpoint ∧
                      Cont firstBound secondBound compositeBound ∧
                        Cont firstLedger secondLedger compositeLedger ∧
                          PkgSig bundle firstProvenance pkg ∧
                            PkgSig bundle secondProvenance pkg ∧
                              PkgSig bundle compositeLedger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro firstCarrier secondCarrier endpointRoute boundRoute ledgerRoute compositePkg
  obtain ⟨_sourceUnary, _middleUnary, firstEndpointUnary, firstBoundUnary, firstLedgerUnary,
    _firstTransportUnary, _firstContinuationUnary, _firstProvenanceUnary, _firstNameUnary,
    firstProvenancePkg, _firstNamePkg⟩ := firstCarrier
  obtain ⟨_middleUnarySecond, _targetUnary, secondEndpointUnary, secondBoundUnary,
    secondLedgerUnary, _secondTransportUnary, _secondContinuationUnary,
    _secondProvenanceUnary, _secondNameUnary, secondProvenancePkg, _secondNamePkg⟩ :=
    secondCarrier
  have compositeEndpointUnary : UnaryHistory compositeEndpoint :=
    unary_cont_closed firstEndpointUnary secondEndpointUnary endpointRoute
  have compositeBoundUnary : UnaryHistory compositeBound :=
    unary_cont_closed firstBoundUnary secondBoundUnary boundRoute
  have compositeLedgerUnary : UnaryHistory compositeLedger :=
    unary_cont_closed firstLedgerUnary secondLedgerUnary ledgerRoute
  exact
    ⟨compositeEndpointUnary, compositeBoundUnary, compositeLedgerUnary, endpointRoute,
      boundRoute, ledgerRoute, firstProvenancePkg, secondProvenancePkg, compositePkg⟩

end BEDC.Derived.BoundedLinearOperatorUp
