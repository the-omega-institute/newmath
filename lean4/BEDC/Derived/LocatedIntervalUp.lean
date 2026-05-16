import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedIntervalPacket [AskSetup] [PackageSetup]
    (lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rationalCells ∧
    UnaryHistory dyadicRefinements ∧ UnaryHistory streamWindows ∧ UnaryHistory readbacks ∧
      UnaryHistory seals ∧ UnaryHistory nameCert ∧ Cont lower upper rationalCells ∧
        Cont rationalCells dyadicRefinements endpoint ∧ Cont streamWindows readbacks transport ∧
          Cont transport seals routes ∧ Cont routes nameCert provenance ∧
            PkgSig bundle endpoint pkg

theorem LocatedIntervalPacket_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          Cont lower' upper' rationalCells' ->
            Cont rationalCells' dyadicRefinements endpoint' ->
              PkgSig bundle endpoint' pkg ->
                LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements
                    streamWindows readbacks seals transport routes provenance nameCert endpoint'
                    bundle pkg ∧
                  hsame rationalCells rationalCells' ∧ hsame endpoint endpoint' := by
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute endpointPkg
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, windowsUnary,
    readbacksUnary, sealsUnary, nameCertUnary, rationalCellsOld, endpointOld,
    transportRoute, routesRoute, provenanceRoute, _endpointPkg⟩ := packet
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have rationalCellsUnary' : UnaryHistory rationalCells' :=
    unary_cont_closed lowerUnary' upperUnary' rationalCellsRoute
  have sameRationalCells : hsame rationalCells rationalCells' :=
    cont_respects_hsame sameLower sameUpper rationalCellsOld rationalCellsRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary' dyadicUnary endpointRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRationalCells (hsame_refl dyadicRefinements) endpointOld
      endpointRoute
  exact
    ⟨⟨lowerUnary', upperUnary', rationalCellsUnary', dyadicUnary, windowsUnary, readbacksUnary,
        sealsUnary, nameCertUnary, rationalCellsRoute, endpointRoute, transportRoute,
        routesRoute, provenanceRoute, endpointPkg⟩,
      sameRationalCells, sameEndpoint⟩

theorem LocatedIntervalPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem LocatedIntervalPacket_dyadic_refinement_handoff [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont rationalCells dyadicRefinements endpoint' ->
        UnaryHistory endpoint' ∧ hsame endpoint endpoint' := by
  intro packet endpointRoute
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, _windowsUnary,
    _readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointOld,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl rationalCells) (hsame_refl dyadicRefinements) endpointOld
      endpointRoute
  exact ⟨endpointUnary, sameEndpoint⟩

theorem LocatedIntervalPacket_endpoint_cell_route_totality [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint cell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont endpoint streamWindows cell ->
        PkgSig bundle cell pkg ->
          UnaryHistory endpoint ∧ UnaryHistory streamWindows ∧ UnaryHistory cell ∧
            Cont rationalCells dyadicRefinements endpoint ∧ Cont endpoint streamWindows cell ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle cell pkg := by
  intro packet endpointCellRoute cellPkg
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    _readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary endpointCellRoute
  exact
    ⟨endpointUnary, streamWindowsUnary, cellUnary, endpointRoute, endpointCellRoute,
      endpointPkg, cellPkg⟩

theorem LocatedIntervalPacket_real_seal_non_escape [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont seals routes sealConsumer ->
        PkgSig bundle sealConsumer pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory streamWindows ∧
            UnaryHistory readbacks ∧ UnaryHistory seals ∧ UnaryHistory sealConsumer ∧
              Cont streamWindows readbacks transport ∧ Cont transport seals routes ∧
                Cont seals routes sealConsumer ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle sealConsumer pkg := by
  intro packet sealsRoutesSealConsumer sealConsumerPkg
  obtain ⟨lowerUnary, upperUnary, _rationalCellsUnary, _dyadicUnary, windowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed sealsUnary routesUnary sealsRoutesSealConsumer
  exact
    ⟨lowerUnary, upperUnary, windowsUnary, readbacksUnary, sealsUnary, sealConsumerUnary,
      transportRoute, routesRoute, sealsRoutesSealConsumer, endpointPkg, sealConsumerPkg⟩

theorem LocatedIntervalPacket_real_seal_ledger_scope [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont seals routes sealConsumer ->
        PkgSig bundle sealConsumer pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rationalCells ∧
            UnaryHistory dyadicRefinements ∧ UnaryHistory streamWindows ∧
              UnaryHistory readbacks ∧ UnaryHistory seals ∧ UnaryHistory sealConsumer ∧
                Cont lower upper rationalCells ∧
                  Cont rationalCells dyadicRefinements endpoint ∧
                    Cont streamWindows readbacks transport ∧ Cont transport seals routes ∧
                      Cont seals routes sealConsumer ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle sealConsumer pkg := by
  intro packet sealsRoutesSealConsumer sealConsumerPkg
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, windowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, rationalCellsRoute, endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed sealsUnary routesUnary sealsRoutesSealConsumer
  exact
    ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, windowsUnary, readbacksUnary,
      sealsUnary, sealConsumerUnary, rationalCellsRoute, endpointRoute, transportRoute,
      routesRoute, sealsRoutesSealConsumer, endpointPkg, sealConsumerPkg⟩

theorem LocatedIntervalPacket_containment_transport_scope [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' cell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg →
      hsame lower lower' →
        hsame upper upper' →
          Cont lower' upper' rationalCells' →
            Cont rationalCells' dyadicRefinements endpoint' →
              Cont endpoint' streamWindows cell →
                PkgSig bundle endpoint' pkg →
                  PkgSig bundle cell pkg →
                    UnaryHistory lower' ∧ UnaryHistory upper' ∧ UnaryHistory rationalCells' ∧
                      UnaryHistory endpoint' ∧ UnaryHistory cell ∧
                        Cont lower' upper' rationalCells' ∧
                          Cont rationalCells' dyadicRefinements endpoint' ∧
                            Cont endpoint' streamWindows cell ∧
                              hsame rationalCells rationalCells' ∧ hsame endpoint endpoint' ∧
                                PkgSig bundle cell pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute cellRoute endpointPkg cellPkg
  have moved :=
    LocatedIntervalPacket_endpoint_transport (lower' := lower') (upper' := upper')
      (rationalCells' := rationalCells') (endpoint' := endpoint') packet sameLower sameUpper
      rationalCellsRoute endpointRoute endpointPkg
  have movedPacket :
      LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements streamWindows
        readbacks seals transport routes provenance nameCert endpoint' bundle pkg :=
    moved.left
  have sameRationalCells : hsame rationalCells rationalCells' :=
    moved.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    moved.right.right
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    _readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := movedPacket
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary cellRoute
  exact
    ⟨lowerUnary, upperUnary, rationalCellsUnary, endpointUnary, cellUnary,
      rationalCellsRoute, endpointRoute, cellRoute, sameRationalCells, sameEndpoint, cellPkg⟩

theorem LocatedIntervalPacket_stream_readback_cell_compatibility [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' cell readback :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg →
      hsame lower lower' →
        hsame upper upper' →
          Cont lower' upper' rationalCells' →
            Cont rationalCells' dyadicRefinements endpoint' →
              Cont endpoint' streamWindows cell →
                Cont streamWindows readbacks readback →
                  PkgSig bundle endpoint' pkg →
                    PkgSig bundle cell pkg →
                      PkgSig bundle readback pkg →
                        UnaryHistory lower' ∧ UnaryHistory upper' ∧
                          UnaryHistory rationalCells' ∧ UnaryHistory endpoint' ∧
                            UnaryHistory cell ∧ UnaryHistory readback ∧
                              Cont lower' upper' rationalCells' ∧
                                Cont rationalCells' dyadicRefinements endpoint' ∧
                                  Cont endpoint' streamWindows cell ∧
                                    Cont streamWindows readbacks readback ∧
                                      hsame rationalCells rationalCells' ∧
                                        hsame endpoint endpoint' ∧ PkgSig bundle cell pkg ∧
                                          PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute cellRoute readbackRoute
    endpointPkg cellPkg readbackPkg
  have moved :=
    LocatedIntervalPacket_endpoint_transport (lower' := lower') (upper' := upper')
      (rationalCells' := rationalCells') (endpoint' := endpoint') packet sameLower sameUpper
      rationalCellsRoute endpointRoute endpointPkg
  have movedPacket :
      LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements streamWindows
        readbacks seals transport routes provenance nameCert endpoint' bundle pkg :=
    moved.left
  have sameRationalCells : hsame rationalCells rationalCells' :=
    moved.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    moved.right.right
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := movedPacket
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary cellRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  exact
    ⟨lowerUnary,
      upperUnary,
      rationalCellsUnary,
      endpointUnary,
      cellUnary,
      readbackUnary,
      rationalCellsRoute,
      endpointRoute,
      cellRoute,
      readbackRoute,
      sameRationalCells,
      sameEndpoint,
      cellPkg,
      readbackPkg⟩

theorem LocatedIntervalPacket_endpoint_window_readback_exhaustion [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont streamWindows readbacks readback ->
        PkgSig bundle readback pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory streamWindows ∧
            UnaryHistory readbacks ∧ UnaryHistory readback ∧
              Cont streamWindows readbacks readback ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro packet readbackRoute readbackPkg
  obtain ⟨lowerUnary, upperUnary, _rationalCellsUnary, _dyadicUnary, streamWindowsUnary,
    readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  exact
    ⟨lowerUnary, upperUnary, streamWindowsUnary, readbacksUnary, readbackUnary,
      readbackRoute, readbackPkg⟩

theorem LocatedIntervalPacket_endpoint_cell_seal_factorization [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint cell readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg →
      Cont endpoint streamWindows cell →
        Cont streamWindows readbacks readback →
          Cont seals routes sealRead →
            PkgSig bundle cell pkg →
              PkgSig bundle readback pkg →
                PkgSig bundle sealRead pkg →
                  UnaryHistory endpoint ∧ UnaryHistory cell ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ Cont rationalCells dyadicRefinements endpoint ∧
                      Cont endpoint streamWindows cell ∧
                        Cont streamWindows readbacks readback ∧ Cont transport seals routes ∧
                          Cont seals routes sealRead ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle cell pkg ∧ PkgSig bundle readback pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet endpointCellRoute readbackRoute sealRoute cellPkg readbackPkg sealPkg
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    _transportRoute, routesRoute, _provenanceRoute, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary endpointCellRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed
      (unary_cont_closed streamWindowsUnary readbacksUnary _transportRoute) sealsUnary routesRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨endpointUnary, cellUnary, readbackUnary, sealUnary, endpointRoute, endpointCellRoute,
      readbackRoute, routesRoute, sealRoute, endpointPkg, cellPkg, readbackPkg, sealPkg⟩

theorem LocatedIntervalPacket_rational_dyadic_cell_chain [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint endpointPrime cell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont rationalCells dyadicRefinements endpointPrime ->
        Cont endpointPrime streamWindows cell ->
          PkgSig bundle endpointPrime pkg ->
            PkgSig bundle cell pkg ->
              UnaryHistory rationalCells ∧ UnaryHistory dyadicRefinements ∧
                UnaryHistory endpointPrime ∧ UnaryHistory cell ∧
                  Cont rationalCells dyadicRefinements endpointPrime ∧
                    Cont endpointPrime streamWindows cell ∧ hsame endpoint endpointPrime ∧
                      PkgSig bundle endpointPrime pkg ∧ PkgSig bundle cell pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet endpointPrimeRoute cellRoute endpointPrimePkg cellPkg
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    _readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointPrimeRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointPrimeUnary streamWindowsUnary cellRoute
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl rationalCells) (hsame_refl dyadicRefinements)
      endpointRoute endpointPrimeRoute
  exact
    ⟨rationalCellsUnary, dyadicUnary, endpointPrimeUnary, cellUnary, endpointPrimeRoute,
      cellRoute, sameEndpoint, endpointPrimePkg, cellPkg⟩

theorem LocatedIntervalPacket_dyadic_real_seal_handoff [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint endpointPrime readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont rationalCells dyadicRefinements endpointPrime ->
        Cont streamWindows readbacks readback ->
          Cont seals routes sealRead ->
            PkgSig bundle endpointPrime pkg ->
              PkgSig bundle readback pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory endpointPrime ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ Cont rationalCells dyadicRefinements endpointPrime ∧
                      Cont streamWindows readbacks readback ∧ Cont transport seals routes ∧
                        Cont seals routes sealRead ∧ hsame endpoint endpointPrime ∧
                          PkgSig bundle endpointPrime pkg ∧ PkgSig bundle readback pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet endpointPrimeRoute readbackRoute sealReadRoute endpointPrimePkg readbackPkg
    sealReadPkg
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointPrimeRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamWindowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealsUnary routesUnary sealReadRoute
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl rationalCells) (hsame_refl dyadicRefinements)
      endpointRoute endpointPrimeRoute
  exact
    ⟨endpointPrimeUnary, readbackUnary, sealReadUnary, endpointPrimeRoute, readbackRoute,
      routesRoute, sealReadRoute, sameEndpoint, endpointPrimePkg, readbackPkg, sealReadPkg⟩

theorem LocatedIntervalPacket_kernel_scope_package [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' readback
      sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          Cont lower' upper' rationalCells' ->
            Cont rationalCells' dyadicRefinements endpoint' ->
              Cont streamWindows readbacks readback ->
                Cont seals routes sealConsumer ->
                  PkgSig bundle endpoint' pkg ->
                    PkgSig bundle readback pkg ->
                      PkgSig bundle sealConsumer pkg ->
                        LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements
                            streamWindows readbacks seals transport routes provenance nameCert
                            endpoint' bundle pkg ∧
                          UnaryHistory endpoint' ∧ UnaryHistory readback ∧
                            UnaryHistory sealConsumer ∧ hsame rationalCells rationalCells' ∧
                              hsame endpoint endpoint' ∧ Cont streamWindows readbacks readback ∧
                                Cont seals routes sealConsumer ∧
                                  PkgSig bundle sealConsumer pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute readbackRoute sealRoute
    endpointPkg _readbackPkg sealPkg
  have moved :=
    LocatedIntervalPacket_endpoint_transport (lower' := lower') (upper' := upper')
      (rationalCells' := rationalCells') (endpoint' := endpoint') packet sameLower sameUpper
      rationalCellsRoute endpointRoute endpointPkg
  have movedPacket :
      LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements streamWindows
        readbacks seals transport routes provenance nameCert endpoint' bundle pkg :=
    moved.left
  have sameRationalCells : hsame rationalCells rationalCells' :=
    moved.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    moved.right.right
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    _transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := movedPacket
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed
      (unary_cont_closed streamWindowsUnary readbacksUnary _transportRoute) sealsUnary routesRoute
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨moved.left, endpointUnary, readbackUnary, sealConsumerUnary, sameRationalCells,
      sameEndpoint, readbackRoute, sealRoute, sealPkg⟩

theorem LocatedIntervalPacket_public_export_packet [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' cell readback
      sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg →
      hsame lower lower' →
        hsame upper upper' →
          Cont lower' upper' rationalCells' →
            Cont rationalCells' dyadicRefinements endpoint' →
              Cont endpoint' streamWindows cell →
                Cont streamWindows readbacks readback →
                  Cont seals routes sealConsumer →
                    PkgSig bundle endpoint' pkg →
                      PkgSig bundle cell pkg →
                        PkgSig bundle readback pkg →
                          PkgSig bundle sealConsumer pkg →
                            LocatedIntervalPacket lower' upper' rationalCells'
                                dyadicRefinements streamWindows readbacks seals transport routes
                                provenance nameCert endpoint' bundle pkg ∧
                              UnaryHistory cell ∧ UnaryHistory readback ∧
                                UnaryHistory sealConsumer ∧ hsame rationalCells rationalCells' ∧
                                  hsame endpoint endpoint' ∧ PkgSig bundle cell pkg ∧
                                    PkgSig bundle readback pkg ∧
                                      PkgSig bundle sealConsumer pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute cellRoute readbackRoute
    sealRoute endpointPkg cellPkg readbackPkg sealPkg
  have moved :=
    LocatedIntervalPacket_endpoint_transport (lower' := lower') (upper' := upper')
      (rationalCells' := rationalCells') (endpoint' := endpoint') packet sameLower sameUpper
      rationalCellsRoute endpointRoute endpointPkg
  have movedPacket :
      LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements streamWindows
        readbacks seals transport routes provenance nameCert endpoint' bundle pkg :=
    moved.left
  have sameRationalCells : hsame rationalCells rationalCells' :=
    moved.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    moved.right.right
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := movedPacket
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed endpointUnary streamWindowsUnary cellRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamWindowsUnary readbacksUnary readbackRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamWindowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨moved.left, cellUnary, readbackUnary, sealUnary, sameRationalCells, sameEndpoint,
      cellPkg, readbackPkg, sealPkg⟩

theorem LocatedIntervalPacket_endpoint_order_window [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint orderRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont lower upper orderRead ->
        Cont seals routes sealRead ->
          PkgSig bundle orderRead pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory orderRead ∧
                UnaryHistory sealRead ∧ Cont lower upper orderRead ∧
                  Cont seals routes sealRead ∧ PkgSig bundle orderRead pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory LocatedIntervalPacket
  intro packet orderRoute sealRoute orderPkg sealPkg
  obtain ⟨lowerUnary, upperUnary, _rationalCellsUnary, _dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, _endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed lowerUnary upperUnary orderRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamWindowsUnary readbacksUnary transportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary sealsUnary routesRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, sealUnary, orderRoute, sealRoute, orderPkg,
      sealPkg⟩

end BEDC.Derived.LocatedIntervalUp
