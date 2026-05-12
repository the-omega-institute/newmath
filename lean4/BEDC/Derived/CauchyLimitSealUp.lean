import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CauchyLimitSealUp
