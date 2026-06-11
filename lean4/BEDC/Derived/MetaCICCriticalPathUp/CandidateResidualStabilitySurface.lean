import BEDC.Derived.MetaCICCriticalPathUp.CandidateResidualStability

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathCandidateResidualStabilitySurface [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead frontierRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  MetaCICCriticalPathCandidateMediatedFrontier strongNorm normalForm obstruction unblock
      discharge handoff continuation provenance localName dyadic stream regseq realSeal
      bundle pkg ∧
    Cont handoff discharge residualRead ∧ Cont residualRead realSeal frontierRead ∧
      PkgSig bundle frontierRead pkg

theorem MetaCICCriticalPathCandidateResidualStabilitySurface_certificate [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathCandidateResidualStabilitySurface strongNorm normalForm obstruction
        unblock discharge handoff continuation provenance localName dyadic stream regseq
        realSeal residualRead frontierRead bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row frontierRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
          hsame ∧
        UnaryHistory residualRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro surface
  exact
    MetaCICCriticalPathCandidateResidualStability surface.left surface.right.left
      surface.right.right.left surface.right.right.right

end BEDC.Derived.MetaCICCriticalPathUp
