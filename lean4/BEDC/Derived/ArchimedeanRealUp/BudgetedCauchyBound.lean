import BEDC.Derived.ArchimedeanRealUp

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanRealCarrier_budgeted_cauchy_bound [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert budget cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      UnaryHistory budget ->
        Cont streamWindow budget cauchyRead ->
          Cont cauchyRead dyadicBound boundLedger ->
            PkgSig bundle cauchyRead pkg ->
              UnaryHistory realName ∧ UnaryHistory streamWindow ∧ UnaryHistory budget ∧
                UnaryHistory cauchyRead ∧ UnaryHistory boundLedger ∧
                  Cont streamWindow budget cauchyRead ∧
                    Cont cauchyRead dyadicBound boundLedger ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: ArchimedeanRealCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier budgetUnary streamBudgetCauchy cauchyDyadicLedger cauchyPkg
  obtain ⟨realNameUnary, _ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, provenancePkg, _localCertPkg⟩ :=
    carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed streamWindowUnary budgetUnary streamBudgetCauchy
  have boundLedgerUnary : UnaryHistory boundLedger :=
    unary_cont_closed cauchyUnary dyadicBoundUnary cauchyDyadicLedger
  exact
    ⟨realNameUnary, streamWindowUnary, budgetUnary, cauchyUnary, boundLedgerUnary,
      streamBudgetCauchy, cauchyDyadicLedger, provenancePkg, cauchyPkg⟩

end BEDC.Derived.ArchimedeanRealUp
