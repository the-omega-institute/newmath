import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRatCoreOpenPhaseExitCriterion [AskSetup] [PackageSetup]
    {mantissa exponent ledger provenance endpoint stream regseq realSeal exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCorePackageCarrier mantissa exponent ledger provenance endpoint bundle pkg ->
      UnaryHistory stream ->
        UnaryHistory realSeal ->
          Cont endpoint stream regseq ->
            Cont regseq realSeal exitRead ->
              PkgSig bundle exitRead pkg ->
                UnaryHistory endpoint ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
                  UnaryHistory realSeal ∧ UnaryHistory exitRead ∧
                    Cont endpoint stream regseq ∧ Cont regseq realSeal exitRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle exitRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier streamUnary realSealUnary regseqRoute exitRoute exitPkg
  obtain ⟨mantissaCarrier, exponentUnary, ledgerUnary, provenanceRoute, endpointRoute,
    endpointPkg⟩ := carrier
  have mantissaUnary : UnaryHistory mantissa :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp mantissaCarrier)).left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed exponentUnary ledgerUnary provenanceRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary mantissaUnary endpointRoute
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed endpointUnary streamUnary regseqRoute
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realSealUnary exitRoute
  exact
    ⟨endpointUnary, streamUnary, regseqUnary, realSealUnary, exitUnary, regseqRoute,
      exitRoute, endpointPkg, exitPkg⟩

end BEDC.Derived.DyadicRatCoreUp
