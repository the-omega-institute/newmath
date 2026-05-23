import BEDC.Derived.LocatedIntervalUp

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalUp_StdBridge [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint cell readback sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont endpoint streamWindows cell ->
        Cont streamWindows readbacks readback ->
          Cont seals routes sealConsumer ->
            PkgSig bundle cell pkg ->
              PkgSig bundle readback pkg ->
                PkgSig bundle sealConsumer pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        LocatedIntervalPacket lower upper rationalCells dyadicRefinements
                            streamWindows readbacks seals transport routes provenance nameCert
                            endpoint bundle pkg ∧ hsame row nameCert)
                      (fun row : BHist =>
                        LocatedIntervalPacket lower upper rationalCells dyadicRefinements
                            streamWindows readbacks seals transport routes provenance nameCert
                            endpoint bundle pkg ∧ hsame row nameCert)
                      (fun row : BHist =>
                        LocatedIntervalPacket lower upper rationalCells dyadicRefinements
                            streamWindows readbacks seals transport routes provenance nameCert
                            endpoint bundle pkg ∧ hsame row nameCert)
                      hsame ∧
                    UnaryHistory cell ∧ UnaryHistory readback ∧ UnaryHistory sealConsumer ∧
                      Cont endpoint streamWindows cell ∧
                        Cont streamWindows readbacks readback ∧
                          Cont seals routes sealConsumer ∧ PkgSig bundle cell pkg ∧
                            PkgSig bundle readback pkg ∧ PkgSig bundle sealConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet cellRoute readbackRoute sealRoute cellPkg readbackPkg sealPkg
  have packetWitness := packet
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    transportRoute, routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have cert :
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
          hsame :=
    LocatedIntervalPacket_semantic_name_certificate packetWitness
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
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed sealsUnary routesUnary sealRoute
  exact
    ⟨cert, cellUnary, readbackUnary, sealConsumerUnary, cellRoute, readbackRoute, sealRoute,
      cellPkg, readbackPkg, sealPkg⟩

end BEDC.Derived.LocatedIntervalUp
