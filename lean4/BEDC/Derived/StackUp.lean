import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
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

def StackBHistCarrier [AskSetup] [PackageSetup]
    (site groupoid objects arrows restriction descent representability provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory site ∧ UnaryHistory groupoid ∧ UnaryHistory arrows ∧ UnaryHistory descent ∧
    UnaryHistory provenance ∧ Cont site groupoid objects ∧ Cont objects arrows restriction ∧
      Cont restriction descent representability ∧ Cont representability provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem StackBHistCarrier_descent_obligation [AskSetup] [PackageSetup]
    {site groupoid objects arrows restriction descent representability provenance endpoint descent'
      representability' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackBHistCarrier site groupoid objects arrows restriction descent representability provenance
        endpoint bundle pkg ->
      hsame descent descent' ->
      Cont restriction descent' representability' ->
      Cont representability' provenance endpoint' ->
      PkgSig bundle endpoint' pkg ->
      StackBHistCarrier site groupoid objects arrows restriction descent' representability'
          provenance endpoint' bundle pkg ∧
        hsame representability representability' ∧ hsame endpoint endpoint' := by
  intro carrier sameDescent representabilityCont' endpointCont' pkgSig'
  have descentUnary' : UnaryHistory descent' :=
    unary_transport carrier.right.right.right.left sameDescent
  have sameRepresentability : hsame representability representability' :=
    cont_respects_hsame (hsame_refl restriction) sameDescent
      carrier.right.right.right.right.right.right.right.left representabilityCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRepresentability (hsame_refl provenance)
      carrier.right.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨carrier.left,
        carrier.right.left,
        carrier.right.right.left,
        descentUnary',
        carrier.right.right.right.right.left,
        carrier.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.left,
        representabilityCont',
        endpointCont',
        pkgSig'⟩,
      sameRepresentability,
      sameEndpoint⟩

theorem StackDescent_obligation_surface [AskSetup] [PackageSetup]
    {site objectRows arrowRows descentLedger carrierRow : BHist}
    {schemeBundle sheafBundle : ProbeBundle ProbeName} {schemePkg sheafPkg : Pkg} :
    UnaryHistory site -> UnaryHistory objectRows -> UnaryHistory arrowRows ->
      Cont objectRows arrowRows descentLedger -> Cont site descentLedger carrierRow ->
        PkgSig schemeBundle site schemePkg -> PkgSig sheafBundle descentLedger sheafPkg ->
          UnaryHistory carrierRow ∧ hsame carrierRow (append site descentLedger) ∧
            Cont objectRows arrowRows descentLedger ∧ PkgSig sheafBundle descentLedger sheafPkg := by
  intro siteUnary objectRowsUnary arrowRowsUnary descentCont carrierCont _schemePkgSig sheafPkgSig
  have descentUnary : UnaryHistory descentLedger :=
    unary_cont_closed objectRowsUnary arrowRowsUnary descentCont
  have carrierUnary : UnaryHistory carrierRow :=
    unary_cont_closed siteUnary descentUnary carrierCont
  exact ⟨carrierUnary, carrierCont, descentCont, sheafPkgSig⟩

theorem StackCarrierPacket_public_surface [AskSetup] [PackageSetup]
    {site sheaf object arrow transport restriction provenance carrier endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory site ->
      UnaryHistory sheaf ->
        UnaryHistory object ->
          UnaryHistory arrow ->
            UnaryHistory transport ->
              UnaryHistory restriction ->
                UnaryHistory provenance ->
                  Cont site sheaf carrier ->
                    Cont object arrow transport ->
                      Cont carrier restriction endpoint ->
                        PkgSig bundle endpoint pkg ->
                          UnaryHistory carrier ∧ UnaryHistory endpoint ∧
                            hsame carrier (append site sheaf) ∧
                              hsame transport (append object arrow) ∧
                                hsame endpoint (append carrier restriction) ∧
                                  PkgSig bundle endpoint pkg := by
  intro siteUnary sheafUnary objectUnary arrowUnary _ restrictionUnary _ siteSheafCarrier
  intro objectArrowTransport carrierRestrictionEndpoint endpointPkg
  have carrierUnary : UnaryHistory carrier :=
    unary_cont_closed siteUnary sheafUnary siteSheafCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrierUnary restrictionUnary carrierRestrictionEndpoint
  exact And.intro carrierUnary
    (And.intro endpointUnary
      (And.intro siteSheafCarrier
        (And.intro objectArrowTransport
          (And.intro carrierRestrictionEndpoint endpointPkg))))

theorem StackCarrierSurface_carrier_obligation [AskSetup] [PackageSetup]
    {scheme sheaf objectRow arrowRow transportRow restrictionRow provenance siteLedger
      groupoidLedger routeLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont scheme sheaf siteLedger ->
      Cont objectRow arrowRow groupoidLedger ->
        Cont transportRow restrictionRow routeLedger ->
          Cont siteLedger groupoidLedger provenance ->
            Cont provenance routeLedger endpoint ->
              PkgSig bundle endpoint pkg ->
                hsame siteLedger (append scheme sheaf) ∧
                  hsame groupoidLedger (append objectRow arrowRow) ∧
                    hsame routeLedger (append transportRow restrictionRow) ∧
                      hsame endpoint (append provenance routeLedger) ∧
                        PkgSig bundle endpoint pkg := by
  intro siteRow groupoidRow routeRow _provenanceRow endpointRow pkgSig
  exact And.intro siteRow
    (And.intro groupoidRow
      (And.intro routeRow
        (And.intro endpointRow pkgSig)))

end BEDC.Derived.StackUp
