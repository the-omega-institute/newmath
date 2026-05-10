import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Derived.SchemeUp
import BEDC.Derived.SheafUp

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.SchemeUp
open BEDC.Derived.SheafUp

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
    (site object arrow restriction descent provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  SheafBHistPointGermLedger site object arrow descent ∧
    UnaryHistory arrow ∧ UnaryHistory restriction ∧ Cont descent restriction endpoint ∧
      UnaryHistory provenance ∧ PkgSig bundle provenance pkg

theorem StackBHistCarrier_descent_obligation [AskSetup] [PackageSetup]
    {site object arrow restriction descent provenance endpoint descent' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackBHistCarrier site object arrow restriction descent provenance endpoint bundle pkg ->
      hsame descent descent' ->
        Cont descent' restriction endpoint' ->
          StackBHistCarrier site object arrow restriction descent' provenance endpoint'
              bundle pkg ∧
            hsame endpoint endpoint' := by
  intro carrier sameDescent endpointCont'
  have descentCont' : Cont object arrow descent' :=
    cont_result_hsame_transport carrier.left.right.right sameDescent
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameDescent (hsame_refl restriction)
      carrier.right.right.right.left endpointCont'
  exact
    ⟨⟨⟨carrier.left.left, carrier.left.right.left, descentCont'⟩,
        carrier.right.left,
        carrier.right.right.left,
        endpointCont',
        carrier.right.right.right.right.left,
        carrier.right.right.right.right.right⟩,
      sameEndpoint⟩

theorem StackBHistCarrier_obligation_surface [AskSetup] [PackageSetup]
    {site object arrow restriction descent provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackBHistCarrier site object arrow restriction descent provenance endpoint bundle pkg ->
      SheafBHistPointGermLedger site object arrow descent ∧
        Cont descent restriction endpoint ∧ UnaryHistory endpoint ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  have descentUnary : UnaryHistory descent :=
    unary_cont_closed carrier.left.right.left carrier.right.left carrier.left.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed descentUnary carrier.right.right.left carrier.right.right.right.left
  exact And.intro carrier.left
    (And.intro carrier.right.right.right.left
      (And.intro endpointUnary carrier.right.right.right.right.right))

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

theorem StackCarrier_obligation_surface
    {point openHist «section» germ site object arrow restriction package : BHist} :
    SchemeSingletonPackage point openHist «section» germ site object arrow restriction ->
      SheafBHistPointGermLedger point openHist «section» germ ->
        Cont restriction arrow package ->
          hsame package (append restriction arrow) ->
            UnaryHistory point ∧ SheafBHistPointGermLedger point openHist «section» germ ∧
              SchemeSingletonPackage point openHist «section» germ site object arrow restriction ∧
                Cont restriction arrow package ∧ hsame package (append restriction arrow) := by
  intro schemePackage sheafLedger restrictionRow _samePackage
  have packageReadback : hsame package (append restriction arrow) :=
    restrictionRow
  exact And.intro sheafLedger.left
    (And.intro sheafLedger
      (And.intro schemePackage
        (And.intro restrictionRow packageReadback)))

end BEDC.Derived.StackUp
