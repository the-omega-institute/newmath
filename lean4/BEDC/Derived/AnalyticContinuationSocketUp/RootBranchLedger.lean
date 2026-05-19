import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_root_branch_ledger [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      nonlocal boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame nonlocal branch →
        Cont nonlocal transport boundary →
          PkgSig bundle boundary pkg →
            UnaryHistory branch ∧ UnaryHistory nonlocal ∧ UnaryHistory boundary ∧
              Cont nonlocal transport boundary ∧ Cont branch transport continuation ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameNonlocalBranch nonlocalTransportBoundary boundaryPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, _outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have nonlocalUnary : UnaryHistory nonlocal :=
    unary_transport branchUnary (hsame_symm sameNonlocalBranch)
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed nonlocalUnary transportUnary nonlocalTransportBoundary
  exact
    ⟨branchUnary, nonlocalUnary, boundaryUnary, nonlocalTransportBoundary,
      branchTransportContinuation, provenancePkg, boundaryPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
