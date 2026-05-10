import BEDC.Derived.GaloisGroupUp

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismActionPacket_unit_automorphism_row
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      identity unitLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      Cont endpoint BHist.Empty identity ->
        Cont identity action unitLedger ->
          UnaryHistory identity ∧ UnaryHistory unitLedger ∧ hsame identity endpoint ∧
            hsame unitLedger (append endpoint action) ∧ hsame endpoint (append provenance ledger) ∧
              PkgSig bundle endpoint pkg := by
  intro packet identityCont unitLedgerCont
  have identityRow :=
    GaloisGroupAutomorphismActionPacket_identity_automorphism_row packet identityCont
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed identityRow.left packet.right.right.right.left unitLedgerCont
  have sameUnitLedger : hsame unitLedger (append endpoint action) := by
    cases identityRow.right.left
    exact unitLedgerCont
  exact And.intro identityRow.left
    (And.intro unitLedgerUnary
      (And.intro identityRow.right.left
        (And.intro sameUnitLedger
          (And.intro identityRow.right.right.left identityRow.right.right.right))))

theorem GaloisGroupAutomorphismActionPacket_identity_action_row
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      identity fixedBaseIdentity : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      Cont BHist.Empty endpoint identity ->
        Cont fixedBase BHist.Empty fixedBaseIdentity ->
          UnaryHistory identity ∧ UnaryHistory fixedBaseIdentity ∧ hsame identity endpoint ∧
            hsame fixedBaseIdentity fixedBase ∧ hsame endpoint (append provenance ledger) ∧
              PkgSig bundle endpoint pkg := by
  intro packet identityCont fixedBaseIdentityCont
  have rows :=
    GaloisGroupAutomorphismActionPacket_fixed_base_carrier_obligation packet
  have sameIdentity : hsame identity endpoint :=
    cont_left_unit_result identityCont
  have sameFixedBaseIdentity : hsame fixedBaseIdentity fixedBase :=
    cont_right_unit_result fixedBaseIdentityCont
  have identityUnary : UnaryHistory identity :=
    unary_cont_closed unary_empty rows.right.right.right.left identityCont
  have fixedBaseIdentityUnary : UnaryHistory fixedBaseIdentity :=
    unary_cont_closed packet.right.right.left unary_empty fixedBaseIdentityCont
  exact And.intro identityUnary
    (And.intro fixedBaseIdentityUnary
      (And.intro sameIdentity
        (And.intro sameFixedBaseIdentity
          (And.intro rows.right.right.right.right.right.right.right.left
            rows.right.right.right.right.right.right.right.right))))

theorem GaloisGroupAutomorphismActionPacket_inverse_action_boundary
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      inverseRow inverseEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      Cont inverse BHist.Empty inverseRow ->
        Cont inverseRow provenance inverseEndpoint ->
          UnaryHistory inverseRow ∧ UnaryHistory inverseEndpoint ∧ hsame inverseRow inverse ∧
            hsame inverseEndpoint (append inverse provenance) ∧ PkgSig bundle endpoint pkg := by
  intro packet inverseRowCont inverseEndpointCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.left
  have sameInverseRow : hsame inverseRow inverse :=
    cont_right_unit_result inverseRowCont
  have inverseRowUnary : UnaryHistory inverseRow :=
    unary_transport packet.right.right.right.right.right.left (hsame_symm sameInverseRow)
  have inverseEndpointUnary : UnaryHistory inverseEndpoint :=
    unary_cont_closed inverseRowUnary provenanceUnary inverseEndpointCont
  have sameInverseEndpoint : hsame inverseEndpoint (append inverse provenance) := by
    cases sameInverseRow
    exact inverseEndpointCont
  exact And.intro inverseRowUnary
    (And.intro inverseEndpointUnary
      (And.intro sameInverseRow
        (And.intro sameInverseEndpoint
          packet.right.right.right.right.right.right.right.right.right.right)))

end BEDC.Derived.GaloisGroupUp
