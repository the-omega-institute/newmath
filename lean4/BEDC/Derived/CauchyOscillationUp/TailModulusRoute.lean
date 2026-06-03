import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationTailModulusRoute [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      windowRead thresholdRead toleranceRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg →
      Cont tailWindow modulus windowRead →
        Cont windowRead tolerance thresholdRead →
          Cont thresholdRead ledger toleranceRead →
            Cont toleranceRead sealRow sealRead →
              Cont tailWindow modulus tolerance →
                Cont tolerance ledger regularRead →
                  Cont routes nameCert sealRead →
                    PkgSig bundle sealRead pkg →
                      hsame sealRead
                          (append (append (append (append tailWindow modulus) tolerance) ledger)
                            sealRow) ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist => hsame row sealRead ∧ Cont ledger sealRow routes)
                            (fun row : BHist =>
                              hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier tailModulusWindow windowToleranceThreshold thresholdLedgerTolerance
    toleranceSealRead tailModulusTolerance toleranceLedgerRegular routesNameCertSealRead
    sealReadPkg
  have carrierRows :
      CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg :=
    carrier
  obtain ⟨_tailWindowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailModulus,
    _modulusTolerance, ledgerSealRoutes, _routesNameCert, provenancePkg⟩ := carrier
  have exposure :
      hsame sealRead
          (append (append (append (append tailWindow modulus) tolerance) ledger) sealRow) ∧
        UnaryHistory sealRead :=
    CauchyOscillationCarrier_tail_window_exposure carrierRows tailModulusWindow
      windowToleranceThreshold thresholdLedgerTolerance toleranceSealRead
  have regular :
      UnaryHistory regularRead ∧
        SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus tolerance ∧
              Cont tolerance ledger regularRead ∧ PkgSig bundle provenance pkg)
          hsame :=
    CauchyOscillationCarrier_regseqrat_handoff carrierRows tailModulusTolerance
      toleranceLedgerRegular provenancePkg
  have sealData :
      UnaryHistory sealRead ∧ Cont ledger sealRow routes ∧ Cont routes nameCert sealRead ∧
        PkgSig bundle sealRead pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row sealRead ∧ Cont ledger sealRow routes)
            (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
            hsame :=
    CauchyOscillationCarrier_seal_handoff_factorization carrierRows ledgerSealRoutes
      routesNameCertSealRead sealReadPkg
  exact ⟨exposure.left, regular.left, exposure.right, sealData.right.right.right.right⟩

end BEDC.Derived.CauchyOscillationUp
