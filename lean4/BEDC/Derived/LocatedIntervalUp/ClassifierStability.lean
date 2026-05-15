import BEDC.Derived.LocatedIntervalUp

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalPacket_classifier_stability [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' dyadicRefinements' streamWindows'
      readbacks' seals' transport' routes' provenance' nameCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame dyadicRefinements dyadicRefinements' ->
            hsame streamWindows streamWindows' ->
              hsame readbacks readbacks' ->
                hsame seals seals' ->
                  hsame routes routes' ->
                    hsame nameCert nameCert' ->
                      Cont lower' upper' rationalCells' ->
                        Cont rationalCells' dyadicRefinements' endpoint' ->
                          Cont streamWindows' readbacks' transport' ->
                            Cont transport' seals' routes' ->
                              Cont routes' nameCert' provenance' ->
                                PkgSig bundle endpoint' pkg ->
                                  LocatedIntervalPacket lower' upper' rationalCells'
                                      dyadicRefinements' streamWindows' readbacks' seals'
                                      transport' routes' provenance' nameCert' endpoint'
                                      bundle pkg ∧
                                    hsame rationalCells rationalCells' ∧
                                      hsame endpoint endpoint' ∧ hsame transport transport' ∧
                                        hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig LocatedIntervalPacket
  intro packet sameLower sameUpper sameDyadic sameWindows sameReadbacks sameSeals sameRoutes
    sameNameCert rationalCellsRoute endpointRoute transportRoute routesRoute provenanceRoute
    endpointPkg
  obtain ⟨lowerUnary, upperUnary, _rationalCellsUnary, dyadicUnary, windowsUnary,
    readbacksUnary, sealsUnary, nameCertUnary, rationalCellsOld, endpointOld, transportOld,
    routesOld, provenanceOld, _endpointPkg⟩ := packet
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have dyadicUnary' : UnaryHistory dyadicRefinements' :=
    unary_transport dyadicUnary sameDyadic
  have windowsUnary' : UnaryHistory streamWindows' :=
    unary_transport windowsUnary sameWindows
  have readbacksUnary' : UnaryHistory readbacks' :=
    unary_transport readbacksUnary sameReadbacks
  have sealsUnary' : UnaryHistory seals' :=
    unary_transport sealsUnary sameSeals
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  have rationalCellsUnary' : UnaryHistory rationalCells' :=
    unary_cont_closed lowerUnary' upperUnary' rationalCellsRoute
  have sameRationalCells : hsame rationalCells rationalCells' :=
    cont_respects_hsame sameLower sameUpper rationalCellsOld rationalCellsRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary' dyadicUnary' endpointRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRationalCells sameDyadic endpointOld endpointRoute
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameWindows sameReadbacks transportOld transportRoute
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRoutes sameNameCert provenanceOld provenanceRoute
  exact
    ⟨⟨lowerUnary', upperUnary', rationalCellsUnary', dyadicUnary', windowsUnary',
        readbacksUnary', sealsUnary', nameCertUnary', rationalCellsRoute, endpointRoute,
        transportRoute, routesRoute, provenanceRoute, endpointPkg⟩,
      sameRationalCells, sameEndpoint, sameTransport, sameProvenance⟩

end BEDC.Derived.LocatedIntervalUp
