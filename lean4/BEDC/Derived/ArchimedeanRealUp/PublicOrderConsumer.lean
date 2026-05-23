import BEDC.Derived.ArchimedeanRealUp

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanRealCarrier_public_order_consumer [AskSetup] [PackageSetup]
    {real bound dyadic window regular ledger transport route provenance name budget threshold
      orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier real bound dyadic window regular ledger transport route provenance
        name bundle pkg ->
      Cont window dyadic budget ->
        Cont bound dyadic threshold ->
          Cont threshold ledger orderRead ->
            PkgSig bundle orderRead pkg ->
              UnaryHistory budget ∧ UnaryHistory threshold ∧ UnaryHistory orderRead ∧
                Cont window dyadic budget ∧ Cont bound dyadic threshold ∧
                  Cont threshold ledger orderRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle orderRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowDyadicBudget boundDyadicThreshold thresholdLedgerOrderRead orderReadPkg
  obtain ⟨_realUnary, boundUnary, dyadicUnary, windowUnary, _regularUnary, ledgerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _realWindowRegular,
    _boundDyadicLedger, _regularLedgerTransport, _transportRouteProvenance,
    _provenancePkg, namePkg⟩ := carrier
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBudget
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed boundUnary dyadicUnary boundDyadicThreshold
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed thresholdUnary ledgerUnary thresholdLedgerOrderRead
  exact
    ⟨budgetUnary, thresholdUnary, orderReadUnary, windowDyadicBudget, boundDyadicThreshold,
      thresholdLedgerOrderRead, namePkg, orderReadPkg⟩

theorem ArchimedeanRealCarrier_integer_bracket [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert floorScale intCandidate bracket : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont dyadicBound ratBound floorScale ->
        Cont floorScale boundLedger intCandidate ->
          Cont intCandidate localCert bracket ->
            PkgSig bundle bracket pkg ->
              UnaryHistory dyadicBound ∧ UnaryHistory floorScale ∧
                UnaryHistory intCandidate ∧ UnaryHistory bracket ∧
                  Cont dyadicBound ratBound floorScale ∧
                    Cont floorScale boundLedger intCandidate ∧
                      Cont intCandidate localCert bracket ∧ PkgSig bundle bracket pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicRatFloor floorLedgerCandidate candidateLocalBracket bracketPkg
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, boundLedgerUnary, _transportUnary, _routesUnary, _provenanceUnary,
    localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have floorUnary : UnaryHistory floorScale :=
    unary_cont_closed dyadicBoundUnary ratBoundUnary dyadicRatFloor
  have candidateUnary : UnaryHistory intCandidate :=
    unary_cont_closed floorUnary boundLedgerUnary floorLedgerCandidate
  have bracketUnary : UnaryHistory bracket :=
    unary_cont_closed candidateUnary localCertUnary candidateLocalBracket
  exact
    ⟨dyadicBoundUnary, floorUnary, candidateUnary, bracketUnary, dyadicRatFloor,
      floorLedgerCandidate, candidateLocalBracket, bracketPkg⟩

end BEDC.Derived.ArchimedeanRealUp
