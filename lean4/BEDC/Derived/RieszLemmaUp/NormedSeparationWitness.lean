import BEDC.Derived.RieszLemmaUp.TasteGate

namespace BEDC.Derived.RieszLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RieszLemmaCarrier_normed_separation_witness [AskSetup] [PackageSetup]
    {source subspace unit tolerance avoidance distance witness complete transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete transport
        replay provenance name bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
              transport replay provenance name bundle pkg ∧ hsame row name)
          (fun _row : BHist =>
            RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
              transport replay provenance name bundle pkg ∧ Cont source subspace unit ∧
                Cont avoidance distance witness ∧ Cont transport replay provenance)
          (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
          hsame ∧
        Cont source subspace unit ∧ Cont avoidance distance witness ∧
          Cont transport replay provenance := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro carrier
  have cert :=
    RieszLemmaCarrier_namecert_obligations
      (source := source) (subspace := subspace) (unit := unit) (tolerance := tolerance)
      (avoidance := avoidance) (distance := distance) (witness := witness)
      (complete := complete) (transport := transport) (replay := replay)
      (provenance := provenance) (name := name) (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨_sourceUnary, _subspaceUnary, _unitUnary, _toleranceUnary, _avoidanceUnary,
    _distanceUnary, _witnessUnary, _completeUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, sourceSubspaceUnit, avoidanceDistanceWitness,
    transportReplayProvenance, _provenancePkg, _namePkg⟩ := carrier
  exact ⟨cert, sourceSubspaceUnit, avoidanceDistanceWitness, transportReplayProvenance⟩

end BEDC.Derived.RieszLemmaUp
