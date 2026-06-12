import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierNormalFormWitnessExtraction
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier normalWitness l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier normalForm normalWitness →
          Cont normalWitness realSeal l10Read →
            PkgSig bundle l10Read pkg →
              UnaryHistory frontier ∧ UnaryHistory normalWitness ∧ UnaryHistory l10Read ∧
                PkgSig bundle realSeal pkg ∧ PkgSig bundle l10Read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro ledger continuationLocalNameFrontier frontierNormalFormWitness
    witnessRealSealL10Read l10ReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameFrontier
  have normalWitnessUnary : UnaryHistory normalWitness :=
    unary_cont_closed frontierUnary normalFormUnary frontierNormalFormWitness
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed normalWitnessUnary realSealUnary witnessRealSealL10Read
  exact ⟨frontierUnary, normalWitnessUnary, l10ReadUnary, realSealPkg, l10ReadPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
