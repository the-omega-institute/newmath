import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionPublicExportPackage [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead diagonalRead
      obstructionRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont trace route traceRead ->
        Cont diagonal halt diagonalRead ->
          Cont traceRead diagonalRead obstructionRead ->
            Cont obstructionRead cert exportRead ->
              PkgSig bundle exportRead pkg ->
                UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧
                  UnaryHistory obstructionRead ∧ UnaryHistory exportRead ∧
                    Cont trace route traceRead ∧ Cont diagonal halt diagonalRead ∧
                      Cont traceRead diagonalRead obstructionRead ∧
                        Cont obstructionRead cert exportRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro carrier traceRouteRead diagonalHaltRead traceDiagonalObstruction
    obstructionCertExport exportPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed traceReadUnary diagonalReadUnary traceDiagonalObstruction
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed obstructionReadUnary certUnary obstructionCertExport
  exact
    ⟨traceReadUnary, diagonalReadUnary, obstructionReadUnary, exportReadUnary,
      traceRouteRead, diagonalHaltRead, traceDiagonalObstruction, obstructionCertExport,
      provenancePkg, exportPkg⟩

theorem HaltingDistinctionRootInscriptionTraceTotality [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert inscriptionRead traceReplay
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont diagonal trace inscriptionRead ->
        Cont trace route traceReplay ->
          Cont inscriptionRead traceReplay rootRead ->
            PkgSig bundle rootRead pkg ->
              UnaryHistory inscriptionRead ∧ UnaryHistory traceReplay ∧
                UnaryHistory rootRead ∧ Cont diagonal trace inscriptionRead ∧
                  Cont trace route traceReplay ∧ Cont inscriptionRead traceReplay rootRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalTraceRead traceRouteReplay inscriptionTraceRoot rootPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have inscriptionReadUnary : UnaryHistory inscriptionRead :=
    unary_cont_closed diagonalUnary traceUnary diagonalTraceRead
  have traceReplayUnary : UnaryHistory traceReplay :=
    unary_cont_closed traceUnary routeUnary traceRouteReplay
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed inscriptionReadUnary traceReplayUnary inscriptionTraceRoot
  exact
    ⟨inscriptionReadUnary, traceReplayUnary, rootReadUnary, diagonalTraceRead,
      traceRouteReplay, inscriptionTraceRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.HaltingDistinctionUp
