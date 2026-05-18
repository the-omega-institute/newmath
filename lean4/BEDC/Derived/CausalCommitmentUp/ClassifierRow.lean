import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def CausalCommitmentClassifierRow [AskSetup] [PackageSetup]
    (observed regularity gap forward locality transport continuation provenance localCert
      observed' regularity' gap' forward' locality' transport' continuation' provenance'
      localCert' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
      continuation provenance localCert bundle pkg ∧
    CausalCommitmentForwardGapCarrier observed' regularity' gap' forward' locality'
      transport' continuation' provenance' localCert' bundle pkg ∧
      hsame observed observed' ∧ hsame regularity regularity' ∧ hsame gap gap' ∧
        hsame forward forward' ∧ hsame locality locality' ∧ hsame localCert localCert'

theorem CausalCommitmentClassifierRow_coherence [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observed' regularity' gap' forward' locality' transport' continuation' provenance'
      localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentClassifierRow observed regularity gap forward locality transport
        continuation provenance localCert observed' regularity' gap' forward' locality'
        transport' continuation' provenance' localCert' bundle pkg ->
      PkgSig bundle localCert pkg ∧ PkgSig bundle localCert' pkg ∧
        hsame observed observed' ∧ hsame regularity regularity' ∧ hsame gap gap' ∧
          hsame forward forward' ∧ hsame locality locality' ∧ hsame localCert localCert' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame
  intro row
  obtain ⟨leftCarrier, rightCarrier, sameObserved, sameRegularity, sameGap, sameForward,
    sameLocality, sameLocalCert⟩ := row
  have leftBase :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    leftCarrier.left
  have rightBase :
      CausalCommitmentCarrier observed' regularity' gap' forward' transport'
        continuation' provenance' localCert' bundle pkg :=
    rightCarrier.left
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, leftPkg⟩ := leftBase
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rightPkg⟩ := rightBase
  exact
    ⟨leftPkg, rightPkg, sameObserved, sameRegularity, sameGap, sameForward, sameLocality,
      sameLocalCert⟩

end BEDC.Derived.CausalCommitmentUp
