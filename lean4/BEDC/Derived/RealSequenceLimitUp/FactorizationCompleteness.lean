import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp.FactorizationCompleteness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealSequenceLimitUp

theorem RealSequenceLimitFactorizationCompleteness [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name criterionTail
      regularTail realSeal auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequence limit window dyadic classifier transport replay provenance
        name bundle pkg →
      Cont classifier window criterionTail →
        Cont criterionTail replay regularTail →
          Cont regularTail transport realSeal →
            Cont realSeal provenance auditRead →
              PkgSig bundle auditRead pkg →
                UnaryHistory classifier ∧ UnaryHistory criterionTail ∧
                  UnaryHistory regularTail ∧ UnaryHistory realSeal ∧ UnaryHistory auditRead ∧
                    Cont classifier window criterionTail ∧
                      Cont criterionTail replay regularTail ∧
                        Cont regularTail transport realSeal ∧
                          Cont realSeal provenance auditRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier classifierWindowTail criterionTailReplayRegular regularTailTransportSeal
    realSealProvenanceAudit auditPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, _dyadicUnary, classifierUnary,
      transportUnary, replayUnary, provenanceUnary, _nameUnary, _sequenceWindowReplay,
      _limitDyadicClassifier, _transportSame, _replaySame, _provenancePkg, namePkg⟩
  have criterionTailUnary : UnaryHistory criterionTail :=
    unary_cont_closed classifierUnary windowUnary classifierWindowTail
  have regularTailUnary : UnaryHistory regularTail :=
    unary_cont_closed criterionTailUnary replayUnary criterionTailReplayRegular
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularTailUnary transportUnary regularTailTransportSeal
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceAudit
  exact
    ⟨classifierUnary, criterionTailUnary, regularTailUnary, realSealUnary, auditReadUnary,
      classifierWindowTail, criterionTailReplayRegular, regularTailTransportSeal,
      realSealProvenanceAudit, namePkg, auditPkg⟩

end BEDC.Derived.RealSequenceLimitUp.FactorizationCompleteness
