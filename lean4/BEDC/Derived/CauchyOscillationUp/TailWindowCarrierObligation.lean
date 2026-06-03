import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_tail_window_carrier_obligation [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      tailRead toleranceRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg ->
      Cont tailWindow modulus tailRead ->
        Cont tailRead tolerance toleranceRead ->
          Cont toleranceRead ledger budgetRead ->
            PkgSig bundle provenance pkg ->
              UnaryHistory tailRead ∧ UnaryHistory toleranceRead ∧
                UnaryHistory budgetRead ∧
                  hsame budgetRead (append (append (append tailWindow modulus) tolerance) ledger) ∧
                    Cont tailWindow modulus tailRead ∧ Cont tailRead tolerance toleranceRead ∧
                      Cont toleranceRead ledger budgetRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier tailModulusRead tailReadToleranceRead toleranceReadLedgerBudget
    provenancePkg
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, _sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, _carrierPkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailWindowUnary modulusUnary tailModulusRead
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailReadUnary toleranceUnary tailReadToleranceRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed toleranceReadUnary ledgerUnary toleranceReadLedgerBudget
  have sameTailRead : hsame tailRead (append tailWindow modulus) := tailModulusRead
  have sameToleranceRead : hsame toleranceRead (append (append tailWindow modulus) tolerance) := by
    cases sameTailRead
    exact tailReadToleranceRead
  have sameBudget :
      hsame budgetRead (append (append (append tailWindow modulus) tolerance) ledger) := by
    cases sameToleranceRead
    exact toleranceReadLedgerBudget
  exact
    ⟨tailReadUnary,
      toleranceReadUnary,
      budgetReadUnary,
      sameBudget,
      tailModulusRead,
      tailReadToleranceRead,
      toleranceReadLedgerBudget,
      provenancePkg⟩

end BEDC.Derived.CauchyOscillationUp
