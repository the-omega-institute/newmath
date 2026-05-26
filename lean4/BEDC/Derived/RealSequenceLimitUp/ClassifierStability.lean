import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitClassifierStability [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name transportedClassifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      hsame classifierRow transportedClassifier ->
        UnaryHistory transportedClassifier ∧
          RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger
            transportedClassifier transport route provenance name bundle pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sameClassifier
  rcases carrier with
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, classifierUnary, transportUnary,
      routeUnary, provenanceUnary, nameUnary, routeCont, classifierCont, transportSame,
      routeSame, provenancePkg, namePkg⟩
  have transportedUnary : UnaryHistory transportedClassifier :=
    unary_transport classifierUnary sameClassifier
  have transportedCont : Cont limitRow dyadicLedger transportedClassifier :=
    cont_result_hsame_transport classifierCont sameClassifier
  have routeTransported : hsame route transportedClassifier :=
    hsame_trans routeSame sameClassifier
  exact
    ⟨transportedUnary,
      ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, transportedUnary, transportUnary,
        routeUnary, provenanceUnary, nameUnary, routeCont, transportedCont, transportSame,
        routeTransported, provenancePkg, namePkg⟩⟩

end BEDC.Derived.RealSequenceLimitUp
