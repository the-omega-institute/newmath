import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StackCarrierPacket [AskSetup] [PackageSetup]
    (site objectRows arrowRows transportRows restrictionRows descentRows representabilityRows
      provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory site ∧ UnaryHistory objectRows ∧ UnaryHistory arrowRows ∧
    UnaryHistory transportRows ∧ UnaryHistory restrictionRows ∧ UnaryHistory descentRows ∧
      UnaryHistory representabilityRows ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ Cont objectRows arrowRows ledger ∧
          Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem StackCarrierPacket_descent_transport [AskSetup] [PackageSetup]
    {site objectRows arrowRows transportRows restrictionRows descentRows representabilityRows
      provenance ledger endpoint objectRows' arrowRows' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackCarrierPacket site objectRows arrowRows transportRows restrictionRows descentRows
        representabilityRows provenance ledger endpoint bundle pkg ->
      hsame objectRows objectRows' ->
        hsame arrowRows arrowRows' ->
          Cont objectRows' arrowRows' ledger' ->
            Cont provenance ledger' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                StackCarrierPacket site objectRows' arrowRows' transportRows restrictionRows
                    descentRows representabilityRows provenance ledger' endpoint' bundle pkg ∧
                  hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameObject sameArrow ledgerCont' endpointCont' pkgSig'
  obtain ⟨siteUnary, objectUnary, arrowUnary, transportUnary, restrictionUnary,
    descentUnary, representabilityUnary, provenanceUnary, _ledgerUnary, _endpointUnary,
    ledgerCont, endpointCont, _pkgSig⟩ := packet
  have objectUnary' : UnaryHistory objectRows' :=
    unary_transport objectUnary sameObject
  have arrowUnary' : UnaryHistory arrowRows' :=
    unary_transport arrowUnary sameArrow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed objectUnary' arrowUnary' ledgerCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary ledgerUnary' endpointCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameObject sameArrow ledgerCont ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameLedger endpointCont endpointCont'
  exact
    ⟨⟨siteUnary, objectUnary', arrowUnary', transportUnary, restrictionUnary, descentUnary,
        representabilityUnary, provenanceUnary, ledgerUnary', endpointUnary', ledgerCont',
        endpointCont', pkgSig'⟩,
      sameLedger,
      sameEndpoint⟩

end BEDC.Derived.StackUp
