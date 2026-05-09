import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BesselUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BesselRootPacket [AskSetup] [PackageSetup]
    (ode holomorphic order sourceEndpoint targetEndpoint recurrence transport provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ode ∧ UnaryHistory holomorphic ∧ UnaryHistory order ∧
    UnaryHistory sourceEndpoint ∧ UnaryHistory targetEndpoint ∧ UnaryHistory provenance ∧
      Cont sourceEndpoint targetEndpoint recurrence ∧ Cont recurrence order transport ∧
        Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem BesselRootPacket_root_ode_source_obligation [AskSetup] [PackageSetup]
    {ode holomorphic order sourceEndpoint targetEndpoint recurrence transport provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BesselRootPacket ode holomorphic order sourceEndpoint targetEndpoint recurrence transport
        provenance endpoint bundle pkg ->
      UnaryHistory ode ∧ UnaryHistory order ∧ UnaryHistory sourceEndpoint ∧
        UnaryHistory targetEndpoint ∧ UnaryHistory recurrence ∧ UnaryHistory transport ∧
          hsame recurrence (append sourceEndpoint targetEndpoint) ∧
            hsame transport (append recurrence order) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have odeUnary : UnaryHistory ode :=
    packet.left
  have orderUnary : UnaryHistory order :=
    packet.right.right.left
  have sourceUnary : UnaryHistory sourceEndpoint :=
    packet.right.right.right.left
  have targetUnary : UnaryHistory targetEndpoint :=
    packet.right.right.right.right.left
  have recurrenceRow : Cont sourceEndpoint targetEndpoint recurrence :=
    packet.right.right.right.right.right.right.left
  have transportRow : Cont recurrence order transport :=
    packet.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have recurrenceUnary : UnaryHistory recurrence :=
    unary_cont_closed sourceUnary targetUnary recurrenceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed recurrenceUnary orderUnary transportRow
  exact And.intro odeUnary
      (And.intro orderUnary
        (And.intro sourceUnary
          (And.intro targetUnary
            (And.intro recurrenceUnary
              (And.intro transportUnary
                (And.intro recurrenceRow
                  (And.intro transportRow pkgSig)))))))

theorem BesselRootPacket_recurrence_ledger_exactness [AskSetup] [PackageSetup]
    {ode holomorphic order sourceEndpoint targetEndpoint recurrence transport provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BesselRootPacket ode holomorphic order sourceEndpoint targetEndpoint recurrence transport
        provenance endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row transport)
        (fun row : BHist => hsame row transport) (fun row : BHist => hsame row transport) hsame ∧
        UnaryHistory recurrence ∧ UnaryHistory transport ∧
          hsame recurrence (append sourceEndpoint targetEndpoint) ∧
            hsame transport (append recurrence order) ∧
              Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have rows := BesselRootPacket_root_ode_source_obligation packet
  have endpointRow : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert (fun row : BHist => hsame row transport)
        (fun row : BHist => hsame row transport) (fun row : BHist => hsame row transport) hsame := {
    core := {
      carrier_inhabited := Exists.intro transport (hsame_refl transport)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro rows.right.right.right.right.left
      (And.intro rows.right.right.right.right.right.left
        (And.intro rows.right.right.right.right.right.right.left
          (And.intro rows.right.right.right.right.right.right.right.left
            (And.intro endpointRow rows.right.right.right.right.right.right.right.right)))))

theorem BesselRootPacket_holomorphic_consumer_boundary [AskSetup] [PackageSetup]
    {ode holomorphic order sourceEndpoint targetEndpoint recurrence transport provenance
      endpoint holomorphicLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BesselRootPacket ode holomorphic order sourceEndpoint targetEndpoint recurrence transport
        provenance endpoint bundle pkg ->
      Cont holomorphic targetEndpoint holomorphicLedger ->
        UnaryHistory holomorphic ∧ UnaryHistory targetEndpoint ∧
          UnaryHistory holomorphicLedger ∧
            hsame holomorphicLedger (append holomorphic targetEndpoint) ∧
              hsame endpoint (append transport provenance) ∧ PkgSig bundle endpoint pkg := by
  intro packet holomorphicRow
  have holomorphicUnary : UnaryHistory holomorphic :=
    packet.right.left
  have targetUnary : UnaryHistory targetEndpoint :=
    packet.right.right.right.right.left
  have holomorphicLedgerUnary : UnaryHistory holomorphicLedger :=
    unary_cont_closed holomorphicUnary targetUnary holomorphicRow
  have endpointRow : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  exact And.intro holomorphicUnary
    (And.intro targetUnary
      (And.intro holomorphicLedgerUnary
        (And.intro holomorphicRow
          (And.intro endpointRow pkgSig))))

end BEDC.Derived.BesselUp
