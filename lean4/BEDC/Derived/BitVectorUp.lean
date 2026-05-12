import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Package

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def BitVectorPacket [AskSetup] [PackageSetup]
    (length spine ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont length spine ledger ∧
    Cont ledger provenance endpoint ∧
      PkgSig bundle endpoint pkg

theorem BitVectorPacket_carrier_transport [AskSetup] [PackageSetup]
    {length length' spine spine' ledger ledger' provenance provenance' endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame length length' ->
      hsame spine spine' ->
        hsame ledger ledger' ->
          hsame provenance provenance' ->
            BitVectorPacket length spine ledger provenance endpoint bundle pkg ->
              BitVectorPacket length' spine' ledger' provenance' endpoint bundle pkg := by
  intro sameLength sameSpine sameLedger sameProvenance packet
  exact And.intro
    (cont_hsame_transport sameLength sameSpine sameLedger packet.left)
    (And.intro
      (cont_hsame_transport sameLedger sameProvenance (hsame_refl endpoint) packet.right.left)
      packet.right.right)

end BEDC.Derived.BitVectorUp
