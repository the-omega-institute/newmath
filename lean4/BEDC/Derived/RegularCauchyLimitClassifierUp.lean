import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitClassifierCarrier [AskSetup] [PackageSetup]
    (input modulus diagonal windows readback ledger sealRow transportRow routes provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
    UnaryHistory windows ∧ UnaryHistory ledger ∧ UnaryHistory transportRow ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ Cont input modulus diagonal ∧
        Cont diagonal windows readback ∧ Cont readback ledger sealRow ∧
          Cont sealRow transportRow routes ∧ Cont provenance sealRow cert ∧
            hsame cert (append provenance sealRow) ∧ PkgSig bundle cert pkg

theorem RegularCauchyLimitClassifierCarrier_stability [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg ->
      UnaryHistory readback ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
        UnaryHistory cert ∧ Cont diagonal windows readback ∧ Cont readback ledger sealRow ∧
          hsame cert (append provenance sealRow) ∧ PkgSig bundle cert pkg := by
  intro carrier
  rcases carrier with
    ⟨_inputUnary, _modulusUnary, diagonalUnary, windowsUnary, ledgerUnary, _transportUnary,
      _routesUnary, provenanceUnary, _inputModulusDiagonal, diagonalWindowsReadback,
      readbackLedgerSeal, _sealTransportRoutes, provenanceSealCert, sameCert, certPkg⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary ledgerUnary readbackLedgerSeal
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary sealUnary provenanceSealCert
  exact
    ⟨readbackUnary, ledgerUnary, sealUnary, certUnary, diagonalWindowsReadback,
      readbackLedgerSeal, sameCert, certPkg⟩

end BEDC.Derived.RegularCauchyLimitClassifierUp
