import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRatCoreTerminalFourFaceToleranceExhaustion [AskSetup] [PackageSetup]
    {mantissa exponent ledger provenance endpoint streamWindow regseqRead realSeal
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCorePackageCarrier mantissa exponent ledger provenance endpoint bundle pkg ->
      UnaryHistory streamWindow ->
        UnaryHistory realSeal ->
          Cont endpoint streamWindow regseqRead ->
            Cont regseqRead realSeal terminalRead ->
              PkgSig bundle terminalRead pkg ->
                RatHistoryCarrier mantissa ∧ UnaryHistory exponent ∧ UnaryHistory ledger ∧
                  UnaryHistory regseqRead ∧ UnaryHistory terminalRead ∧
                    Cont exponent ledger provenance ∧ Cont provenance mantissa endpoint ∧
                      Cont endpoint streamWindow regseqRead ∧
                        Cont regseqRead realSeal terminalRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory RatHistoryCarrier
  intro carrier streamUnary realSealUnary endpointStreamRoute terminalRoute terminalPkg
  obtain ⟨mantissaCarrier, exponentUnary, ledgerUnary, provenanceRoute, endpointRoute,
    endpointPkg⟩ := carrier
  have mantissaUnary : UnaryHistory mantissa :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp mantissaCarrier)).left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed exponentUnary ledgerUnary provenanceRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary mantissaUnary endpointRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed endpointUnary streamUnary endpointStreamRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed regseqUnary realSealUnary terminalRoute
  exact
    ⟨mantissaCarrier, exponentUnary, ledgerUnary, regseqUnary, terminalUnary,
      provenanceRoute, endpointRoute, endpointStreamRoute, terminalRoute, endpointPkg,
      terminalPkg⟩

end BEDC.Derived.DyadicRatCoreUp
