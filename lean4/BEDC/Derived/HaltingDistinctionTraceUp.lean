import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HaltingDistinctionTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HaltingDistinctionTraceCarrier [AskSetup] [PackageSetup]
    (admitted trace distinction diagonal transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory admitted ∧ UnaryHistory trace ∧ UnaryHistory distinction ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont admitted trace transport ∧
        Cont transport distinction route ∧ Cont route diagonal cert ∧
          PkgSig bundle provenance pkg

theorem HaltingDistinctionTraceDiagonalObstructionPackage [AskSetup] [PackageSetup]
    {admitted trace distinction diagonal transport route provenance cert traceRead diagonalRead
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionTraceCarrier admitted trace distinction diagonal transport route provenance
        cert bundle pkg →
      Cont trace distinction traceRead →
        Cont distinction diagonal diagonalRead →
          Cont traceRead diagonalRead endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory traceRead ∧ UnaryHistory diagonalRead ∧ UnaryHistory endpoint ∧
                Cont trace distinction traceRead ∧ Cont distinction diagonal diagonalRead ∧
                  Cont traceRead diagonalRead endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier traceToDistinction distinctionToDiagonal readEndpoint endpointPkg
  obtain ⟨_admittedUnary, traceUnary, distinctionUnary, diagonalUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _certUnary, _admittedTraceTransport,
    _transportDistinctionRoute, _routeDiagonalCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary distinctionUnary traceToDistinction
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed distinctionUnary diagonalUnary distinctionToDiagonal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceReadUnary diagonalReadUnary readEndpoint
  exact
    ⟨traceReadUnary, diagonalReadUnary, endpointUnary, traceToDistinction,
      distinctionToDiagonal, readEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionTraceUp
