import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive AnalyticContinuationSocketUp : Type where
  | mk
      (source leftOverlap witness operation output branch transport continuation provenance name :
        BHist) :
      AnalyticContinuationSocketUp

def AnalyticContinuationSocketCarrier [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory branch ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory name ∧ Cont source leftOverlap witness ∧
        Cont witness operation output ∧ Cont branch transport continuation ∧
          Cont output continuation provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem AnalyticContinuationSocketCarrier_operation_output_factorization [AskSetup]
    [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output continuation consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory output ∧ UnaryHistory consumer ∧ Cont witness operation output ∧
            Cont output continuation consumer ∧ Cont output continuation provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier outputContinuationConsumer consumerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _branchUnary,
    _transportUnary, continuationUnary, _nameUnary, _sourceLeftOverlapWitness,
    witnessOperationOutput, _branchTransportContinuation, outputContinuationProvenance,
    provenancePkg, _namePkg⟩ := carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed outputUnary continuationUnary outputContinuationConsumer
  exact
    ⟨outputUnary,
      consumerUnary,
      witnessOperationOutput,
      outputContinuationConsumer,
      outputContinuationProvenance,
      provenancePkg,
      consumerPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
