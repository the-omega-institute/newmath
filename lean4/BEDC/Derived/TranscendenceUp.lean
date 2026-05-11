import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TranscendenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.TranscendenceUp
