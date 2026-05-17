import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_selector_exactness [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      source' regular' schedule' witness' ledger' trap' sealRow' transport' route' provenance'
      localCert' gridBudget gridLedger gridClassifier gridTail gridBudget' gridLedger'
      gridClassifier' gridTail' rootRead rootRead' gridSelectorRead gridSelectorRead'
      gridLedgerRead gridLedgerRead' gridClassifierRead gridClassifierRead' gridTailRead
      gridTailRead' realRead realRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      BoundedMonotoneCauchyWitnessCarrier source' regular' schedule' witness' ledger' trap'
        sealRow' transport' route' provenance' localCert' bundle pkg →
        hsame source source' →
          hsame regular regular' →
            hsame gridBudget gridBudget' →
              hsame gridLedger gridLedger' →
                hsame gridClassifier gridClassifier' →
                  hsame gridTail gridTail' →
                    hsame sealRow sealRow' →
                      Cont source regular rootRead →
                        Cont source' regular' rootRead' →
                          Cont rootRead gridBudget gridSelectorRead →
                            Cont rootRead' gridBudget' gridSelectorRead' →
                              Cont gridSelectorRead gridLedger gridLedgerRead →
                                Cont gridSelectorRead' gridLedger' gridLedgerRead' →
                                  Cont gridLedgerRead gridClassifier gridClassifierRead →
                                    Cont gridLedgerRead' gridClassifier' gridClassifierRead' →
                                      Cont gridClassifierRead gridTail gridTailRead →
                                        Cont gridClassifierRead' gridTail' gridTailRead' →
                                          Cont gridTailRead sealRow realRead →
                                            Cont gridTailRead' sealRow' realRead' →
                                              hsame realRead realRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier carrier' sameSource sameRegular sameGridBudget sameGridLedger sameGridClassifier
    sameGridTail sameSealRow sourceRegularRoot sourceRegularRoot' rootGridBudget rootGridBudget'
    gridSelectorGridLedger gridSelectorGridLedger' gridLedgerGridClassifier
    gridLedgerGridClassifier' gridClassifierGridTail gridClassifierGridTail' gridTailSeal
    gridTailSeal'
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  obtain ⟨_sourceUnary', _regularUnary', _scheduleUnary', _witnessUnary', _ledgerUnary',
    _trapUnary', _sealUnary', _provenanceUnary', _sourceScheduleRegular',
    _regularWitnessTrap', _trapSealRoute', _transportLocalCertRoute', _routeProvenanceSeal',
    _provenancePkg'⟩ := carrier'
  have sameRoot : hsame rootRead rootRead' :=
    cont_respects_hsame sameSource sameRegular sourceRegularRoot sourceRegularRoot'
  have sameGridSelector : hsame gridSelectorRead gridSelectorRead' :=
    cont_respects_hsame sameRoot sameGridBudget rootGridBudget rootGridBudget'
  have sameGridLedgerRead : hsame gridLedgerRead gridLedgerRead' :=
    cont_respects_hsame sameGridSelector sameGridLedger gridSelectorGridLedger
      gridSelectorGridLedger'
  have sameGridClassifierRead : hsame gridClassifierRead gridClassifierRead' :=
    cont_respects_hsame sameGridLedgerRead sameGridClassifier gridLedgerGridClassifier
      gridLedgerGridClassifier'
  have sameGridTailRead : hsame gridTailRead gridTailRead' :=
    cont_respects_hsame sameGridClassifierRead sameGridTail gridClassifierGridTail
      gridClassifierGridTail'
  exact cont_respects_hsame sameGridTailRead sameSealRow gridTailSeal gridTailSeal'

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
