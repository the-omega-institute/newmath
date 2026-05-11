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

theorem TranscendenceCarrierPacket_fieldext_source_boundary [AskSetup] [PackageSetup]
    {fieldExtSource family coeffLedger tests transports readbacks endpoint fieldExtSource'
      family' coeffLedger' tests' readbacks' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks
      endpoint bundle pkg ->
    hsame fieldExtSource fieldExtSource' ->
    hsame family family' ->
    hsame coeffLedger coeffLedger' ->
    Cont fieldExtSource' family' tests' ->
    Cont coeffLedger' tests' readbacks' ->
    Cont transports readbacks' endpoint' ->
    PkgSig bundle endpoint' pkg ->
    TranscendenceCarrierPacket fieldExtSource' family' coeffLedger' tests' transports
        readbacks' endpoint' bundle pkg ∧
      hsame tests tests' ∧ hsame readbacks readbacks' ∧ hsame endpoint endpoint' := by
  intro packet sameSource sameFamily sameCoeff testsRow' readbacksRow' endpointRow' pkgSig'
  have sourceUnary : UnaryHistory fieldExtSource := packet.left
  have familyUnary : UnaryHistory family := packet.right.left
  have coeffUnary : UnaryHistory coeffLedger := packet.right.right.left
  have transportsUnary : UnaryHistory transports := packet.right.right.right.right.left
  have sourceUnary' : UnaryHistory fieldExtSource' := unary_transport sourceUnary sameSource
  have familyUnary' : UnaryHistory family' := unary_transport familyUnary sameFamily
  have coeffUnary' : UnaryHistory coeffLedger' := unary_transport coeffUnary sameCoeff
  have testsUnary' : UnaryHistory tests' :=
    unary_cont_closed sourceUnary' familyUnary' testsRow'
  have readbacksUnary' : UnaryHistory readbacks' :=
    unary_cont_closed coeffUnary' testsUnary' readbacksRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed transportsUnary readbacksUnary' endpointRow'
  have testsSame : hsame tests tests' :=
    cont_respects_hsame sameSource sameFamily
      packet.right.right.right.right.right.right.left testsRow'
  have readbacksSame : hsame readbacks readbacks' :=
    cont_respects_hsame sameCoeff testsSame
      packet.right.right.right.right.right.right.right.left readbacksRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl transports) readbacksSame
      packet.right.right.right.right.right.right.right.right.left endpointRow'
  constructor
  · exact And.intro sourceUnary'
      (And.intro familyUnary'
        (And.intro coeffUnary'
          (And.intro testsUnary'
            (And.intro transportsUnary
              (And.intro readbacksUnary'
                (And.intro testsRow'
                  (And.intro readbacksRow'
                    (And.intro endpointRow' pkgSig'))))))))
  · constructor
    · exact testsSame
    · constructor
      · exact readbacksSame
      · exact endpointSame

def TranscendenceClassifier [AskSetup] [PackageSetup]
    (fieldExtSource family coeffLedger tests transports readbacks endpoint fieldExtSource'
      family' coeffLedger' tests' transports' readbacks' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks
      endpoint bundle pkg ∧
    TranscendenceCarrierPacket fieldExtSource' family' coeffLedger' tests' transports'
      readbacks' endpoint' bundle pkg ∧
      hsame fieldExtSource fieldExtSource' ∧ hsame family family' ∧
        hsame coeffLedger coeffLedger' ∧ hsame tests tests' ∧
          hsame transports transports' ∧ hsame readbacks readbacks' ∧
            hsame endpoint endpoint' ∧ Cont coeffLedger' tests' readbacks' ∧
              PkgSig bundle endpoint' pkg

def TranscendenceCarrierPacketClassifier [AskSetup] [PackageSetup]
    (fieldExtSource family coeffLedger tests transports readbacks endpoint fieldExtSource'
      family' coeffLedger' tests' transports' readbacks' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks endpoint
      bundle pkg ∧
    TranscendenceCarrierPacket fieldExtSource' family' coeffLedger' tests' transports' readbacks'
        endpoint' bundle pkg ∧
      hsame fieldExtSource fieldExtSource' ∧ hsame family family' ∧
        hsame coeffLedger coeffLedger' ∧ hsame tests tests' ∧
          hsame transports transports' ∧ hsame readbacks readbacks' ∧ hsame endpoint endpoint'

theorem TranscendenceCarrierPacketClassifier_transport [AskSetup] [PackageSetup]
    {fieldExtSource family coeffLedger tests transports readbacks endpoint fieldExtSource'
      family' coeffLedger' tests' transports' readbacks' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks endpoint
        bundle pkg ->
      hsame fieldExtSource fieldExtSource' ->
        hsame family family' ->
          hsame coeffLedger coeffLedger' ->
            Cont fieldExtSource' family' tests' ->
              Cont coeffLedger' tests' readbacks' ->
                hsame transports transports' ->
                  Cont transports' readbacks' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      TranscendenceCarrierPacketClassifier fieldExtSource family coeffLedger tests
                        transports readbacks endpoint fieldExtSource' family' coeffLedger' tests'
                        transports' readbacks' endpoint' bundle pkg := by
  intro packet sameFieldExt sameFamily sameCoeff fieldFamilyTests'
    coeffTestsReadbacks' sameTransports transportsReadbacksEndpoint' pkgSig'
  rcases packet with
    ⟨fieldExtUnary, familyUnary, coeffUnary, testsUnary, transportsUnary, _readbacksUnary,
      fieldFamilyTests, coeffTestsReadbacks, _transportsReadbacksEndpoint, _pkgSig⟩
  have fieldExtUnary' : UnaryHistory fieldExtSource' :=
    unary_transport fieldExtUnary sameFieldExt
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have coeffUnary' : UnaryHistory coeffLedger' :=
    unary_transport coeffUnary sameCoeff
  have testsSame : hsame tests tests' :=
    cont_respects_hsame sameFieldExt sameFamily fieldFamilyTests fieldFamilyTests'
  have testsUnary' : UnaryHistory tests' :=
    unary_transport testsUnary testsSame
  have readbacksSame : hsame readbacks readbacks' :=
    cont_respects_hsame sameCoeff testsSame coeffTestsReadbacks coeffTestsReadbacks'
  have readbacksUnary' : UnaryHistory readbacks' :=
    unary_transport (unary_cont_closed coeffUnary testsUnary coeffTestsReadbacks) readbacksSame
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransports readbacksSame
      _transportsReadbacksEndpoint transportsReadbacksEndpoint'
  have packetSource :
      TranscendenceCarrierPacket fieldExtSource family coeffLedger tests transports readbacks endpoint
          bundle pkg :=
    ⟨fieldExtUnary, familyUnary, coeffUnary, testsUnary, transportsUnary,
      unary_cont_closed coeffUnary testsUnary coeffTestsReadbacks, fieldFamilyTests,
      coeffTestsReadbacks, _transportsReadbacksEndpoint, _pkgSig⟩
  have packetTarget :
      TranscendenceCarrierPacket fieldExtSource' family' coeffLedger' tests' transports'
          readbacks' endpoint' bundle pkg :=
    ⟨fieldExtUnary', familyUnary', coeffUnary', testsUnary', transportsUnary',
      readbacksUnary', fieldFamilyTests', coeffTestsReadbacks', transportsReadbacksEndpoint',
      pkgSig'⟩
  exact ⟨packetSource, packetTarget, sameFieldExt, sameFamily, sameCoeff, testsSame,
    sameTransports, readbacksSame, endpointSame⟩

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
