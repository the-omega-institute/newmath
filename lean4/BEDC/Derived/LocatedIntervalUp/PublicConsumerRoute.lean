import BEDC.Derived.LocatedIntervalUp

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalPacket_public_consumer_route [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint cell readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont endpoint streamWindows cell ->
        Cont streamWindows readbacks readback ->
          Cont seals routes sealRead ->
            PkgSig bundle cell pkg ->
              PkgSig bundle readback pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rationalCells ∧
                    UnaryHistory dyadicRefinements ∧ UnaryHistory cell ∧
                      UnaryHistory readback ∧ UnaryHistory sealRead ∧
                        Cont endpoint streamWindows cell ∧
                          Cont streamWindows readbacks readback ∧ Cont seals routes sealRead ∧
                            PkgSig bundle endpoint pkg ∧ PkgSig bundle cell pkg ∧
                              PkgSig bundle readback pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet cellRoute readbackRoute sealRoute cellPkg readbackPkg sealPkg
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary cellRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamWindowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, cellUnary, readbackUnary,
      sealReadUnary, cellRoute, readbackRoute, sealRoute, endpointPkg, cellPkg, readbackPkg,
      sealPkg⟩

theorem LocatedIntervalPacket_real_comparison_boundary [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint orderRead endpointPrime readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont lower upper orderRead ->
        Cont rationalCells dyadicRefinements endpointPrime ->
          Cont streamWindows readbacks readback ->
            Cont seals routes sealRead ->
              PkgSig bundle orderRead pkg ->
                PkgSig bundle endpointPrime pkg ->
                  PkgSig bundle readback pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory orderRead ∧ UnaryHistory endpointPrime ∧
                        UnaryHistory readback ∧ UnaryHistory sealRead ∧
                          hsame endpoint endpointPrime ∧ Cont lower upper orderRead ∧
                            Cont rationalCells dyadicRefinements endpointPrime ∧
                              Cont streamWindows readbacks readback ∧
                                Cont seals routes sealRead ∧ PkgSig bundle orderRead pkg ∧
                                  PkgSig bundle endpointPrime pkg ∧
                                    PkgSig bundle readback pkg ∧
                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet orderRoute endpointPrimeRoute readbackRoute sealRoute orderPkg
    endpointPrimePkg readbackPkg sealPkg
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed lowerUnary upperUnary orderRoute
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointPrimeRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamWindowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl rationalCells) (hsame_refl dyadicRefinements)
      endpointRoute endpointPrimeRoute
  exact
    ⟨orderUnary, endpointPrimeUnary, readbackUnary, sealReadUnary, sameEndpoint, orderRoute,
      endpointPrimeRoute, readbackRoute, sealRoute, orderPkg, endpointPrimePkg, readbackPkg,
      sealPkg⟩

end BEDC.Derived.LocatedIntervalUp
