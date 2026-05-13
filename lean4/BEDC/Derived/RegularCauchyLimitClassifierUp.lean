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

theorem RegularCauchyLimitClassifierCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg ->
      hsame sealConsumer sealRow ->
        UnaryHistory sealConsumer ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
          UnaryHistory sealRow ∧ Cont diagonal windows readback ∧ Cont readback ledger sealRow ∧
            hsame cert (append provenance sealRow) ∧ PkgSig bundle cert pkg := by
  intro carrier sameConsumer
  have stable :=
    RegularCauchyLimitClassifierCarrier_stability carrier
  obtain ⟨readbackUnary, ledgerUnary, sealUnary, _certUnary, diagonalWindowsReadback,
    readbackLedgerSeal, sameCert, certPkg⟩ := stable
  have consumerUnary : UnaryHistory sealConsumer :=
    unary_transport_symm sealUnary sameConsumer
  exact
    ⟨consumerUnary, readbackUnary, ledgerUnary, sealUnary, diagonalWindowsReadback,
      readbackLedgerSeal, sameCert, certPkg⟩

theorem RegularCauchyLimitClassifierCarrier_diagonal_window_public_boundary [AskSetup]
    [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg ->
      Cont cert routes publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory readback ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
            UnaryHistory cert ∧ UnaryHistory publicRead ∧ Cont diagonal windows readback ∧
              Cont readback ledger sealRow ∧ Cont cert routes publicRead ∧
                hsame cert (append provenance sealRow) ∧ PkgSig bundle cert pkg ∧
                  PkgSig bundle publicRead pkg := by
  intro carrier certRoutesPublicRead publicReadPkg
  have stable :=
    RegularCauchyLimitClassifierCarrier_stability carrier
  obtain ⟨readbackUnary, ledgerUnary, sealUnary, certUnary, diagonalWindowsReadback,
    readbackLedgerSeal, sameCert, certPkg⟩ := stable
  have routesUnary : UnaryHistory routes :=
    carrier.right.right.right.right.right.right.left
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed certUnary routesUnary certRoutesPublicRead
  exact
    ⟨readbackUnary, ledgerUnary, sealUnary, certUnary, publicReadUnary,
      diagonalWindowsReadback, readbackLedgerSeal, certRoutesPublicRead, sameCert, certPkg,
      publicReadPkg⟩

theorem RegularCauchyLimitClassifierCarrier_public_export [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg ->
      Cont cert routes publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
            UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
              UnaryHistory sealRow ∧ UnaryHistory cert ∧ UnaryHistory publicRead ∧
                Cont input modulus diagonal ∧ Cont diagonal windows readback ∧
                  Cont readback ledger sealRow ∧ Cont provenance sealRow cert ∧
                    Cont cert routes publicRead ∧ hsame cert (append provenance sealRow) ∧
                      PkgSig bundle cert pkg ∧ PkgSig bundle publicRead pkg := by
  intro carrier certRoutesPublicRead publicReadPkg
  have inputUnary : UnaryHistory input :=
    carrier.left
  have modulusUnary : UnaryHistory modulus :=
    carrier.right.left
  have diagonalUnary : UnaryHistory diagonal :=
    carrier.right.right.left
  have windowsUnary : UnaryHistory windows :=
    carrier.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.right.right.left
  have routesUnary : UnaryHistory routes :=
    carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.left
  have inputModulusDiagonal : Cont input modulus diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalWindowsReadback : Cont diagonal windows readback :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have readbackLedgerSeal : Cont readback ledger sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have provenanceSealCert : Cont provenance sealRow cert :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameCert : hsame cert (append provenance sealRow) :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have certPkg : PkgSig bundle cert pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary ledgerUnary readbackLedgerSeal
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary sealUnary provenanceSealCert
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed certUnary routesUnary certRoutesPublicRead
  exact
    ⟨inputUnary, modulusUnary, diagonalUnary, windowsUnary, readbackUnary, ledgerUnary,
      sealUnary, certUnary, publicReadUnary, inputModulusDiagonal, diagonalWindowsReadback,
      readbackLedgerSeal, provenanceSealCert, certRoutesPublicRead, sameCert, certPkg,
      publicReadPkg⟩

theorem RegularCauchyLimitClassifierCarrier_diagonal_seal_uniqueness [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      cert' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg ->
      RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert' bundle pkg ->
        Cont cert routes publicRead ->
          Cont cert' routes publicRead' ->
            hsame publicRead publicRead' := by
  intro carrier carrier' certRoutesPublicRead certRoutesPublicRead'
  have stable :=
    RegularCauchyLimitClassifierCarrier_stability carrier
  have stable' :=
    RegularCauchyLimitClassifierCarrier_stability carrier'
  obtain ⟨_readbackUnary, _ledgerUnary, _sealUnary, _certUnary, _diagonalWindowsReadback,
    _readbackLedgerSeal, sameCert, _certPkg⟩ := stable
  obtain ⟨_readbackUnary', _ledgerUnary', _sealUnary', _certUnary', _diagonalWindowsReadback',
    _readbackLedgerSeal', sameCert', _certPkg'⟩ := stable'
  have sameCerts : hsame cert cert' :=
    hsame_trans sameCert (hsame_symm sameCert')
  exact
    cont_respects_hsame sameCerts (hsame_refl routes) certRoutesPublicRead
      certRoutesPublicRead'

end BEDC.Derived.RegularCauchyLimitClassifierUp
