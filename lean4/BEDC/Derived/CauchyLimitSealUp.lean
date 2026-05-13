import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyLimitSealPacket [AskSetup] [PackageSetup]
    (source schedule ledger diagonal sealed transportRow provenance certificate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory diagonal ∧
    UnaryHistory transportRow ∧ UnaryHistory provenance ∧ Cont schedule source ledger ∧
      Cont ledger diagonal sealed ∧ Cont sealed transportRow provenance ∧
        Cont provenance transportRow certificate ∧ PkgSig bundle certificate pkg

theorem CauchyLimitSealPacket_window_factorization [AskSetup] [PackageSetup]
    {source schedule ledger diagonal sealed transportRow provenance certificate window observation
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealPacket source schedule ledger diagonal sealed transportRow provenance certificate
        bundle pkg ->
      Cont schedule source window ->
        Cont window ledger observation ->
          Cont observation diagonal realRead ->
            hsame ledger observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                Cont schedule source window ∧ Cont window ledger observation ∧
                  Cont observation diagonal realRead ∧ hsame sealed realRead ∧
                    PkgSig bundle certificate pkg := by
  intro packet scheduleSourceWindow windowLedgerObservation observationDiagonalRead
    sameLedgerObservation
  obtain ⟨sourceUnary, scheduleUnary, diagonalUnary, _transportUnary, _provenanceUnary,
    _scheduleSourceLedger, ledgerDiagonalSealed, _sealedTransportProvenance,
    _provenanceTransportCertificate, certificatePkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary sourceUnary _scheduleSourceLedger
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sealedSameRead : hsame sealed realRead :=
    cont_respects_hsame sameLedgerObservation (hsame_refl diagonal) ledgerDiagonalSealed
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, scheduleSourceWindow,
      windowLedgerObservation, observationDiagonalRead, sealedSameRead, certificatePkg⟩

def CauchyLimitSealCarrier [AskSetup] [PackageSetup]
    (source schedule dyadic diagonal «seal» transport provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
    UnaryHistory diagonal ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
        Cont source schedule dyadic ∧ Cont dyadic diagonal «seal» ∧
          Cont «seal» transport provenance ∧ Cont provenance localCert endpoint ∧
            hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg

theorem CauchyLimitSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal «seal» transport provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
        localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem CauchyLimitSealCarrier_realup_consumer_boundary [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont endpoint sealRow realRead ->
        UnaryHistory realRead ∧ Cont endpoint sealRow realRead ∧
          hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg := by
  intro carrier endpointSealRead
  rcases carrier with
    ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, sealUnary,
      _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
      _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
      _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩
  exact
    ⟨unary_cont_closed endpointUnary sealUnary endpointSealRead, endpointSealRead,
      sameEndpoint, endpointPkg⟩

theorem CauchyLimitSealCarrier_verification_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            hsame dyadic observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                hsame sealRow realRead ∧ hsame endpoint (append provenance localCert) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    sameDyadicObservation
  rcases carrier with
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
      _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
      _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
      _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sameSealRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, sameSealRead, sameEndpoint,
      endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
