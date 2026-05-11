import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TranscendenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TranscendenceCarrierPacket [AskSetup] [PackageSetup]
    (fieldExtSource family coeffLedger tests transports readbacks endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExtSource ∧ UnaryHistory family ∧ UnaryHistory coeffLedger ∧
    UnaryHistory tests ∧ UnaryHistory transports ∧ UnaryHistory readbacks ∧
      Cont fieldExtSource family tests ∧ Cont coeffLedger tests readbacks ∧
        Cont transports readbacks endpoint ∧ PkgSig bundle endpoint pkg

theorem TranscendenceCarrierPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {fieldExtSource family coeffLedger tests transports readbacks endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          hsame ∧ Cont fieldExtSource family tests ∧ Cont coeffLedger tests readbacks ∧
            Cont transports readbacks endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have cert :
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks e
                bundle pkg ∧ hsame row e)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint
            (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              cases data with
              | intro packetE sameRowE =>
                  exact Exists.intro e
                    (And.intro packetE (hsame_trans (hsame_symm same) sameRowE))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, packet.right.right.right.right.right.right.left,
    packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
        packet.right.right.right.right.right.right.right.right.right⟩

theorem TranscendenceCarrierPacket_algebraic_independence_ledger [AskSetup]
    [PackageSetup] {fieldExtSource family coeffLedger tests transports readbacks endpoint
      tests' readbacks' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks
        endpoint bundle pkg ->
      hsame tests tests' ->
        Cont coeffLedger tests' readbacks' ->
          Cont transports readbacks' endpoint ->
            TranscendenceCarrierPacket fieldExtSource family coeffLedger tests' transports
                readbacks' endpoint bundle pkg ∧
              hsame readbacks readbacks' ∧ UnaryHistory tests' ∧ UnaryHistory readbacks' ∧
                PkgSig bundle endpoint pkg := by
  intro packet sameTests coeffTestsReadbacks' transportsReadbacksEndpoint'
  rcases packet with
    ⟨fieldExtSourceUnary, familyUnary, coeffLedgerUnary, testsUnary, transportsUnary,
      _readbacksUnary, fieldFamilyTests, coeffTestsReadbacks, _transportsReadbacksEndpoint,
      pkgSig⟩
  have testsUnary' : UnaryHistory tests' :=
    unary_transport testsUnary sameTests
  have fieldFamilyTests' : Cont fieldExtSource family tests' :=
    cont_result_hsame_transport fieldFamilyTests sameTests
  have sameReadbacks : hsame readbacks readbacks' :=
    cont_respects_hsame (hsame_refl coeffLedger) sameTests coeffTestsReadbacks
      coeffTestsReadbacks'
  have readbacksUnary' : UnaryHistory readbacks' :=
    unary_cont_closed coeffLedgerUnary testsUnary' coeffTestsReadbacks'
  have packet' :
      TranscendenceCarrierPacket fieldExtSource family coeffLedger tests' transports
          readbacks' endpoint bundle pkg :=
    ⟨fieldExtSourceUnary, familyUnary, coeffLedgerUnary, testsUnary', transportsUnary,
      readbacksUnary', fieldFamilyTests', coeffTestsReadbacks', transportsReadbacksEndpoint',
      pkgSig⟩
  exact ⟨packet', sameReadbacks, testsUnary', readbacksUnary', pkgSig⟩

end BEDC.Derived.TranscendenceUp
