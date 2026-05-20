import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_zeta_branch_obstruction_exactness [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      zetaRead obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch zetaRead →
        Cont zetaRead transport obstruction →
          PkgSig bundle obstruction pkg →
            UnaryHistory branch ∧ UnaryHistory zetaRead ∧ UnaryHistory obstruction ∧
              hsame zetaRead (append output branch) ∧
                hsame obstruction (append zetaRead transport) ∧
                  Cont branch transport continuation ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle obstruction pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier outputBranchZetaRead zetaReadTransportObstruction obstructionPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_cont_closed outputUnary branchUnary outputBranchZetaRead
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed zetaReadUnary transportUnary zetaReadTransportObstruction
  exact
    ⟨branchUnary, zetaReadUnary, obstructionUnary, outputBranchZetaRead,
      zetaReadTransportObstruction, branchTransportContinuation, provenancePkg, obstructionPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
