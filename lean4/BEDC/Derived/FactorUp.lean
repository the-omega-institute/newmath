import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FactorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FactorBHistSourceCore
    (vna centre witness typeRow ledger endpoint : BHist) : Prop :=
  UnaryHistory vna ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
    Cont vna centre ledger ∧ Cont ledger witness endpoint

theorem FactorBHistSourcePacket_trivial_centre_obligation
    {vna centre witness typeRow ledger endpoint : BHist} :
    FactorBHistSourceCore vna centre witness typeRow ledger endpoint ->
      UnaryHistory vna ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont vna centre ledger ∧
          Cont ledger witness endpoint := by
  intro packet
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary packet.right.right.left packet.right.right.right.right.right
  exact
    ⟨packet.left, packet.right.left, packet.right.right.left, packet.right.right.right.left,
      ledgerUnary, endpointUnary, packet.right.right.right.right.left,
      packet.right.right.right.right.right⟩

def FactorBHistSourcePacket [AskSetup] [PackageSetup]
    (algebra centre witness typeRow transport ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory algebra ∧ UnaryHistory centre ∧ UnaryHistory typeRow ∧ UnaryHistory transport ∧
    Cont algebra centre witness ∧
      Cont witness typeRow ledger ∧ Cont ledger transport endpoint ∧ PkgSig bundle endpoint pkg

theorem FactorBHistSourcePacket_carrier_trivial_centre_obligation [AskSetup] [PackageSetup]
    {algebra centre witness typeRow transport ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      UnaryHistory algebra ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont algebra centre witness ∧
          Cont witness typeRow ledger ∧ Cont ledger transport endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have centreUnary : UnaryHistory centre := packet.right.left
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed packet.left centreUnary packet.right.right.right.right.left
  have typeRowUnary : UnaryHistory typeRow := packet.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed witnessUnary typeRowUnary packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport := packet.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary transportUnary packet.right.right.right.right.right.right.left
  exact
    ⟨packet.left, centreUnary, witnessUnary, typeRowUnary, ledgerUnary, endpointUnary,
      packet.right.right.right.right.left, packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right⟩

theorem FactorBHistSourcePacket_type_classifier_stability_obligation [AskSetup] [PackageSetup]
    {algebra centre witness typeRow transport ledger endpoint typeRow' ledger' endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      hsame typeRow' typeRow -> Cont witness typeRow' ledger' ->
        Cont ledger' transport endpoint' ->
          UnaryHistory typeRow' ∧ UnaryHistory ledger' ∧ UnaryHistory endpoint' ∧
            hsame ledger ledger' ∧ hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg := by
  intro packet sameTypeRow witnessTypeRow' ledgerTransport'
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have typeRowUnary : UnaryHistory typeRow := packet.right.right.left
  have typeRowUnary' : UnaryHistory typeRow' :=
    unary_transport typeRowUnary (hsame_symm sameTypeRow)
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed witnessUnary typeRowUnary' witnessTypeRow'
  have transportUnary : UnaryHistory transport := packet.right.right.right.left
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary' transportUnary ledgerTransport'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl witness) (hsame_symm sameTypeRow)
      packet.right.right.right.right.right.left witnessTypeRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger (hsame_refl transport)
      packet.right.right.right.right.right.right.left ledgerTransport'
  exact
    ⟨typeRowUnary', ledgerUnary', endpointUnary', sameLedger, sameEndpoint,
      packet.right.right.right.right.right.right.right⟩

theorem FactorBHistSourcePacket_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {algebra centre witness typeRow transport ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      UnaryHistory algebra ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ hsame ledger (append witness typeRow) ∧
          hsame endpoint (append ledger transport) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have centreUnary : UnaryHistory centre := packet.right.left
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed packet.left centreUnary packet.right.right.right.right.left
  have typeRowUnary : UnaryHistory typeRow := packet.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed witnessUnary typeRowUnary packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport := packet.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary transportUnary packet.right.right.right.right.right.right.left
  exact
    ⟨packet.left, centreUnary, witnessUnary, typeRowUnary, ledgerUnary, endpointUnary,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right⟩
theorem FactorBHistSourcePacket_centre_ledger_transport_determinacy
    [AskSetup] [PackageSetup]
    {algebra centre centre' witness witness' typeRow transport ledger ledger' endpoint endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      hsame centre' centre -> Cont algebra centre' witness' ->
        Cont witness' typeRow ledger' -> Cont ledger' transport endpoint' ->
          hsame witness witness' ∧ hsame ledger ledger' ∧ hsame endpoint endpoint' ∧
            UnaryHistory witness' ∧ UnaryHistory ledger' ∧ UnaryHistory endpoint' := by
  intro packet sameCentre algebraCentre' witnessTypeRow' ledgerTransport'
  have centreUnary' : UnaryHistory centre' :=
    unary_transport packet.right.left (hsame_symm sameCentre)
  have witnessUnary' : UnaryHistory witness' :=
    unary_cont_closed packet.left centreUnary' algebraCentre'
  have typeRowUnary : UnaryHistory typeRow := packet.right.right.left
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed witnessUnary' typeRowUnary witnessTypeRow'
  have transportUnary : UnaryHistory transport := packet.right.right.right.left
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary' transportUnary ledgerTransport'
  have sameWitness : hsame witness witness' :=
    cont_respects_hsame (hsame_refl algebra) (hsame_symm sameCentre)
      packet.right.right.right.right.left algebraCentre'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameWitness (hsame_refl typeRow)
      packet.right.right.right.right.right.left witnessTypeRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger (hsame_refl transport)
      packet.right.right.right.right.right.right.left ledgerTransport'
  exact
    ⟨sameWitness, sameLedger, sameEndpoint, witnessUnary', ledgerUnary', endpointUnary'⟩

theorem FactorBHistSourcePacket_type_row_no_confusion [AskSetup] [PackageSetup]
    {algebra centre witness typeRow transport ledger endpoint typeRowA typeRowB ledgerA ledgerB
      endpointA endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      hsame typeRowA typeRow ->
        hsame typeRowB typeRow ->
          Cont witness typeRowA ledgerA ->
            Cont witness typeRowB ledgerB ->
              Cont ledgerA transport endpointA ->
                Cont ledgerB transport endpointB ->
                  hsame typeRowA typeRowB ∧ hsame ledgerA ledgerB ∧
                    hsame endpointA endpointB := by
  intro packet sameTypeRowA sameTypeRowB witnessTypeRowA witnessTypeRowB ledgerTransportA
    ledgerTransportB
  have sameTypeRows : hsame typeRowA typeRowB :=
    hsame_trans sameTypeRowA (hsame_symm sameTypeRowB)
  have sameLedgers : hsame ledgerA ledgerB :=
    cont_respects_hsame (hsame_refl witness) sameTypeRows witnessTypeRowA witnessTypeRowB
  have sameEndpoints : hsame endpointA endpointB :=
    cont_respects_hsame sameLedgers (hsame_refl transport) ledgerTransportA ledgerTransportB
  exact ⟨sameTypeRows, sameLedgers, sameEndpoints⟩

theorem FactorBHistSourcePacket_public_bridge_boundary [AskSetup] [PackageSetup]
    {algebra centre centre' witness witness' typeRow transport ledger ledger' endpoint endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      hsame centre' centre ->
        Cont algebra centre' witness' ->
          Cont witness' typeRow ledger' ->
            Cont ledger' transport endpoint' ->
              PkgSig bundle endpoint' pkg ->
                FactorBHistSourcePacket algebra centre' witness' typeRow transport ledger'
                    endpoint' bundle pkg ∧
                  hsame witness witness' ∧ hsame ledger ledger' ∧ hsame endpoint endpoint' ∧
                    PkgSig bundle endpoint pkg := by
  intro packet sameCentre algebraCentre' witnessTypeRow' ledgerTransport' pkgSig'
  have boundary :=
    FactorBHistSourcePacket_centre_ledger_transport_determinacy
      packet sameCentre algebraCentre' witnessTypeRow' ledgerTransport'
  exact
    ⟨⟨packet.left, unary_transport packet.right.left (hsame_symm sameCentre),
        packet.right.right.left, packet.right.right.right.left, algebraCentre',
        witnessTypeRow', ledgerTransport', pkgSig'⟩,
      boundary.left, boundary.right.left, boundary.right.right.left,
      packet.right.right.right.right.right.right.right⟩

theorem FactorBHistSourcePacket_root_threshold_unblock_surface [AskSetup] [PackageSetup]
    {algebra centre witness typeRow transport ledger endpoint consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FactorBHistSourcePacket algebra centre witness typeRow transport ledger endpoint bundle pkg ->
      Cont endpoint transport consumerEndpoint ->
        UnaryHistory consumerEndpoint ∧ hsame consumerEndpoint (append endpoint transport) ∧
          hsame endpoint (append ledger transport) ∧ hsame ledger (append witness typeRow) ∧
            hsame witness (append algebra centre) ∧ PkgSig bundle endpoint pkg := by
  intro packet endpointTransport
  have centreUnary : UnaryHistory centre := packet.right.left
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed packet.left centreUnary packet.right.right.right.right.left
  have typeRowUnary : UnaryHistory typeRow := packet.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed witnessUnary typeRowUnary packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport := packet.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary transportUnary packet.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed endpointUnary transportUnary endpointTransport
  exact
    ⟨consumerUnary, endpointTransport, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.left, packet.right.right.right.right.left,
      packet.right.right.right.right.right.right.right⟩

end BEDC.Derived.FactorUp
