import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationApplicationRowTotality [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      operationRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont application replay operationRead ->
        UnaryHistory branchRead ->
          Cont operationRead branchRead name ->
            PkgSig bundle operationRead pkg ->
              UnaryHistory gamma ∧ UnaryHistory application ∧ UnaryHistory replay ∧
                UnaryHistory operationRead ∧ UnaryHistory branchRead ∧ UnaryHistory name ∧
                  Cont gamma application replay ∧ Cont application replay operationRead ∧
                    Cont operationRead branchRead name ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle operationRead pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier applicationReplayOperation branchReadUnary operationBranchName operationPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, gammaApplicationReplay,
    provenancePkg, namePkg⟩ := carrier
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  exact
    ⟨gammaUnary, applicationUnary, replayUnary, operationReadUnary, branchReadUnary,
      nameUnary, gammaApplicationReplay, applicationReplayOperation, operationBranchName,
      provenancePkg, operationPkg, namePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
