import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StreamDiagonalSelectorPacket [AskSetup] [PackageSetup]
    (schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory selector ∧ UnaryHistory readback ∧
    UnaryHistory diagonalPacket ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ Cont schedule selector window ∧
        Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
          PkgSig bundle endpoint pkg

theorem StreamDiagonalSelectorPacket_real_handoff [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint window' dyadicLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket
        routes provenance nameCert endpoint bundle pkg ->
      Cont schedule selector window' ->
        Cont window' readback dyadicLedger' ->
          Cont dyadicLedger' diagonalPacket endpoint' ->
            PkgSig bundle endpoint' pkg ->
              StreamDiagonalSelectorPacket schedule selector window' readback dyadicLedger'
                  diagonalPacket routes provenance nameCert endpoint' bundle pkg ∧
                hsame window window' ∧ hsame dyadicLedger dyadicLedger' ∧
                  hsame endpoint endpoint' := by
  intro packet windowRoute ledgerRoute endpointRoute endpointPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, routesUnary,
    provenanceUnary, nameCertUnary, windowOld, ledgerOld, endpointOld, _endpointPkg⟩ := packet
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary' : UnaryHistory dyadicLedger' :=
    unary_cont_closed windowUnary' readbackUnary ledgerRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed dyadicLedgerUnary' diagonalUnary endpointRoute
  have sameWindow : hsame window window' :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl selector) windowOld windowRoute
  have sameDyadicLedger : hsame dyadicLedger dyadicLedger' :=
    cont_respects_hsame sameWindow (hsame_refl readback) ledgerOld ledgerRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameDyadicLedger (hsame_refl diagonalPacket) endpointOld endpointRoute
  exact
    ⟨⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, routesUnary, provenanceUnary,
        nameCertUnary, windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩,
      sameWindow, sameDyadicLedger, sameEndpoint⟩

theorem StreamDiagonalSelectorPacket_selector_determinacy [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint windowPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      Cont schedule selector windowPrime ->
        UnaryHistory windowPrime ∧ hsame window windowPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet scheduleSelectorWindowPrime
  obtain ⟨scheduleUnary, selectorUnary, _readbackUnary, _diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, scheduleSelectorWindow, _windowReadbackDyadicLedger,
    _dyadicLedgerDiagonalEndpoint, _endpointPkg⟩ := packet
  have windowPrimeUnary : UnaryHistory windowPrime :=
    unary_cont_closed scheduleUnary selectorUnary scheduleSelectorWindowPrime
  have sameWindow : hsame window windowPrime :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl selector) scheduleSelectorWindow
      scheduleSelectorWindowPrime
  exact ⟨windowPrimeUnary, sameWindow⟩

end BEDC.Derived.StreamDiagonalSelectorUp
