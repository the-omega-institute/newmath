import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRatCoreL10ExitNameCertInterface [AskSetup] [PackageSetup]
    {mantissa exponent ledger provenance endpoint stream regseq realSeal exitRead interfaceRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCorePackageCarrier mantissa exponent ledger provenance endpoint bundle pkg ->
      UnaryHistory stream ->
        UnaryHistory realSeal ->
          Cont endpoint stream regseq ->
            Cont regseq realSeal exitRead ->
              Cont exitRead ledger interfaceRead ->
                PkgSig bundle interfaceRead pkg ->
                  UnaryHistory endpoint ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
                    UnaryHistory realSeal ∧ UnaryHistory exitRead ∧
                      UnaryHistory interfaceRead ∧ Cont endpoint stream regseq ∧
                        Cont regseq realSeal exitRead ∧ Cont exitRead ledger interfaceRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle interfaceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig UnaryHistory
  intro carrier streamUnary realSealUnary endpointStreamRoute exitRoute interfaceRoute
    interfacePkg
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
    unary_cont_closed endpointUnary streamUnary endpointStreamRoute
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realSealUnary exitRoute
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed exitUnary ledgerUnary interfaceRoute
  exact
    ⟨endpointUnary, streamUnary, regseqUnary, realSealUnary, exitUnary, interfaceUnary,
      endpointStreamRoute, exitRoute, interfaceRoute, endpointPkg, interfacePkg⟩

end BEDC.Derived.DyadicRatCoreUp
