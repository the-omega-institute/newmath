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

def AnalyticContinuationSocketPacket [AskSetup] [PackageSetup]
    (source leftOverlap witness operation output branch transport continuation provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
    UnaryHistory operation ∧ UnaryHistory output ∧ UnaryHistory branch ∧
      UnaryHistory provenance ∧ Cont source leftOverlap transport ∧
        Cont witness operation continuation ∧ PkgSig bundle name pkg

theorem AnalyticContinuationSocketPacket_overlap_transport [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketPacket source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      UnaryHistory source ∧ UnaryHistory leftOverlap ∧ UnaryHistory witness ∧
        Cont source leftOverlap transport ∧ Cont witness operation continuation ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨sourceUnary, leftOverlapUnary, witnessUnary, _operationUnary, _outputUnary,
    _branchUnary, _provenanceUnary, overlapRoute, continuationRoute, namePkg⟩ := packet
  exact
    ⟨sourceUnary, leftOverlapUnary, witnessUnary, overlapRoute, continuationRoute, namePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
