import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10ResidualDyadicRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal continuation residualRead →
        PkgSig bundle residualRead pkg →
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
            UnaryHistory realSeal ∧ UnaryHistory residualRead ∧
              Cont dyadic stream regseq ∧ Cont regseq realSeal handoff ∧
                PkgSig bundle realSeal pkg ∧ PkgSig bundle residualRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro ledger sealContinuationResidual residualReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    dyadicStreamRegseq, regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed realSealUnary continuationUnary sealContinuationResidual
  exact
    ⟨dyadicUnary, streamUnary, regseqUnary, realSealUnary, residualUnary,
      dyadicStreamRegseq, regseqRealSealHandoff, realSealPkg, residualReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
