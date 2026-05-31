import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionCarrier_classifier_transport [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonWindow transport replay provenance
      localCert endpoint' observations' regularity' tailModulus' commonWindow' replay'
      consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonWindow transport replay provenance localCert bundle pkg →
      hsame endpoint endpoint' →
        hsame observations observations' →
          hsame regularity regularity' →
            hsame tailModulus tailModulus' →
              hsame commonWindow commonWindow' →
                hsame replay replay' →
                  Cont tailModulus commonWindow observations →
                    Cont observations regularity endpoint →
                      Cont endpoint replay consumer →
                        Cont endpoint' replay' consumer' →
                          PkgSig bundle consumer pkg →
                            PkgSig bundle consumer' pkg →
                              hsame consumer consumer' ∧ UnaryHistory endpoint' ∧
                                UnaryHistory observations' ∧ UnaryHistory regularity' ∧
                                  UnaryHistory tailModulus' ∧ UnaryHistory commonWindow' ∧
                                    UnaryHistory consumer ∧ UnaryHistory consumer' ∧
                                      Cont endpoint replay consumer ∧
                                        Cont endpoint' replay' consumer' ∧
                                          PkgSig bundle consumer pkg ∧
                                            PkgSig bundle consumer' pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sameEndpoint sameObservations sameRegularity sameTailModulus sameCommonWindow
    sameReplay _tailCommonCont _observationsRegularityCont consumerCont consumerCont'
    consumerPkg consumerPkg'
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonWindowUnary, _transportUnary, replayUnary, _provenanceUnary, _localCertUnary,
      _provenancePkg, _localCertPkg⟩ := carrier
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have observationsUnary' : UnaryHistory observations' :=
    unary_transport observationsUnary sameObservations
  have regularityUnary' : UnaryHistory regularity' :=
    unary_transport regularityUnary sameRegularity
  have tailModulusUnary' : UnaryHistory tailModulus' :=
    unary_transport tailModulusUnary sameTailModulus
  have commonWindowUnary' : UnaryHistory commonWindow' :=
    unary_transport commonWindowUnary sameCommonWindow
  have replayUnary' : UnaryHistory replay' :=
    unary_transport replayUnary sameReplay
  have consumerSame : hsame consumer consumer' :=
    cont_respects_hsame sameEndpoint sameReplay consumerCont consumerCont'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary replayUnary consumerCont
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed endpointUnary' replayUnary' consumerCont'
  exact
    ⟨consumerSame, endpointUnary', observationsUnary', regularityUnary', tailModulusUnary',
      commonWindowUnary', consumerUnary, consumerUnary', consumerCont, consumerCont',
      consumerPkg, consumerPkg'⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
