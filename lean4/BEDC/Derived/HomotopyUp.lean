import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HomotopyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HomotopyBHistSourcePacket [AskSetup] [PackageSetup]
    (source target deformation interval provenance endpointRead ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory deformation ∧
    UnaryHistory interval ∧ UnaryHistory provenance ∧ Cont deformation interval endpointRead ∧
      Cont endpointRead provenance ledger ∧ Cont ledger target endpoint ∧
        PkgSig bundle endpoint pkg

theorem HomotopyBHistSourcePacket_interval_parameter_transport [AskSetup] [PackageSetup]
    {source target deformation interval intervalPrime provenance endpointRead endpointReadPrime
      ledger endpoint endpointPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source target deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      hsame interval intervalPrime ->
        Cont deformation intervalPrime endpointReadPrime ->
          Cont endpointReadPrime provenance ledger ->
            Cont ledger target endpointPrime ->
              PkgSig bundle endpointPrime pkg ->
                HomotopyBHistSourcePacket source target deformation intervalPrime provenance
                    endpointReadPrime ledger endpointPrime bundle pkg ∧
                  hsame endpointRead endpointReadPrime ∧ hsame endpoint endpointPrime := by
  intro packet sameInterval endpointReadCont' ledgerCont' endpointCont' pkgSig'
  have intervalUnary' : UnaryHistory intervalPrime :=
    unary_transport packet.right.right.right.left sameInterval
  have endpointReadUnary' : UnaryHistory endpointReadPrime :=
    unary_cont_closed packet.right.right.left intervalUnary' endpointReadCont'
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointReadUnary' packet.right.right.right.right.left ledgerCont'
  have endpointUnary' : UnaryHistory endpointPrime :=
    unary_cont_closed ledgerUnary packet.right.left endpointCont'
  have sameEndpointRead : hsame endpointRead endpointReadPrime :=
    cont_respects_hsame (hsame_refl deformation) sameInterval
      packet.right.right.right.right.right.left endpointReadCont'
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl ledger) (hsame_refl target)
      packet.right.right.right.right.right.right.right.left endpointCont'
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro intervalUnary'
            (And.intro packet.right.right.right.right.left
              (And.intro endpointReadCont'
                (And.intro ledgerCont'
                  (And.intro endpointCont' pkgSig'))))))))
    (And.intro sameEndpointRead sameEndpoint)

theorem HomotopyBHistSourcePacket_interval_endpoint_determinacy [AskSetup] [PackageSetup]
    {source target deformation interval interval' provenance endpointRead endpointRead' ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source target deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      HomotopyBHistSourcePacket source target deformation interval' provenance endpointRead' ledger
        endpoint bundle pkg ->
        hsame endpointRead endpointRead' -> hsame interval interval' := by
  intro leftPacket rightPacket sameEndpointRead
  have rightEndpointReadCont : Cont deformation interval' endpointRead :=
    cont_result_hsame_transport rightPacket.right.right.right.right.right.left
      (hsame_symm sameEndpointRead)
  exact cont_left_cancel leftPacket.right.right.right.right.right.left rightEndpointReadCont

end BEDC.Derived.HomotopyUp
