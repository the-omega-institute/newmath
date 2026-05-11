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

theorem StackRepresentability_boundary [AskSetup] [PackageSetup]
    {site object arrow restriction descent provenance endpoint representability atlas
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackBHistCarrier site object arrow restriction descent provenance endpoint bundle pkg ->
      Cont descent restriction representability ->
        Cont representability site atlas ->
          Cont atlas provenance boundary ->
            UnaryHistory representability ∧ UnaryHistory atlas ∧ UnaryHistory boundary ∧
              hsame representability (append descent restriction) ∧
                hsame atlas (append representability site) ∧
                  hsame boundary (append atlas provenance) ∧ PkgSig bundle provenance pkg := by
  intro carrier representabilityCont atlasCont boundaryCont
  have descentUnary : UnaryHistory descent :=
    unary_cont_closed carrier.left.right.left carrier.right.left carrier.left.right.right
  have representabilityUnary : UnaryHistory representability :=
    unary_cont_closed descentUnary carrier.right.right.left representabilityCont
  have atlasUnary : UnaryHistory atlas :=
    unary_cont_closed representabilityUnary carrier.left.left atlasCont
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed atlasUnary carrier.right.right.right.right.left boundaryCont
  exact
    ⟨representabilityUnary,
      atlasUnary,
      boundaryUnary,
      representabilityCont,
      atlasCont,
      boundaryCont,
      carrier.right.right.right.right.right⟩

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

theorem StackLedger_obligation_surface [AskSetup] [PackageSetup]
    {site cover objectRows arrowRows descentRows representabilityRows routes provenance
      ledger : BHist}
    {schemeBundle sheafBundle : ProbeBundle ProbeName} {schemePkg sheafPkg : Pkg} :
    UnaryHistory site -> UnaryHistory cover -> UnaryHistory objectRows -> UnaryHistory arrowRows ->
      UnaryHistory representabilityRows -> Cont site cover routes ->
        Cont objectRows arrowRows descentRows ->
          Cont descentRows representabilityRows provenance -> Cont routes provenance ledger ->
            PkgSig schemeBundle routes schemePkg -> PkgSig sheafBundle provenance sheafPkg ->
              UnaryHistory descentRows ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
                hsame routes (append site cover) ∧
                  hsame descentRows (append objectRows arrowRows) ∧
                    hsame provenance (append descentRows representabilityRows) ∧
                      hsame ledger (append routes provenance) ∧
                        PkgSig schemeBundle routes schemePkg ∧
                          PkgSig sheafBundle provenance sheafPkg := by
  intro siteUnary coverUnary objectRowsUnary arrowRowsUnary representabilityRowsUnary siteCover
  intro objectArrow descentRepresentability routesProvenance schemePkgSig sheafPkgSig
  have descentUnary : UnaryHistory descentRows :=
    unary_cont_closed objectRowsUnary arrowRowsUnary objectArrow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed descentUnary representabilityRowsUnary descentRepresentability
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed siteUnary coverUnary siteCover
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed routesUnary provenanceUnary routesProvenance
  exact And.intro descentUnary
    (And.intro provenanceUnary
      (And.intro ledgerUnary
        (And.intro siteCover
          (And.intro objectArrow
            (And.intro descentRepresentability
              (And.intro routesProvenance
                (And.intro schemePkgSig sheafPkgSig)))))))
theorem StackCarrierPacket_descent_obligation [AskSetup] [PackageSetup]
    {site sheaf object arrow transport restriction provenance carrier endpoint
      descentEndpoint : BHist}
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
                        Cont transport restriction descentEndpoint ->
                          PkgSig bundle endpoint pkg ->
                            UnaryHistory carrier ∧ UnaryHistory endpoint ∧
                              UnaryHistory descentEndpoint ∧ hsame carrier (append site sheaf) ∧
                                hsame transport (append object arrow) ∧
                                  hsame endpoint (append carrier restriction) ∧
                                    hsame descentEndpoint (append transport restriction) ∧
                                      PkgSig bundle endpoint pkg := by
  intro siteUnary sheafUnary objectUnary arrowUnary _ restrictionUnary _ siteSheafCarrier
  intro objectArrowTransport carrierRestrictionEndpoint transportRestrictionDescent endpointPkg
  have carrierUnary : UnaryHistory carrier :=
    unary_cont_closed siteUnary sheafUnary siteSheafCarrier
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed objectUnary arrowUnary objectArrowTransport
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrierUnary restrictionUnary carrierRestrictionEndpoint
  have descentUnary : UnaryHistory descentEndpoint :=
    unary_cont_closed transportUnary restrictionUnary transportRestrictionDescent
  exact
    ⟨carrierUnary, endpointUnary, descentUnary, siteSheafCarrier, objectArrowTransport,
      carrierRestrictionEndpoint, transportRestrictionDescent, endpointPkg⟩

theorem StackCarrierPacket_descent_rows [AskSetup] [PackageSetup]
    {site cover objectSection arrowSection objectRow arrowRow transportRows restrictionRows
      descentRows representabilityRows provenance ledger endpoint refinedCover gluedObject
      gluedArrow gluedLedger gluedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackCarrierPacket site objectRow arrowRow transportRows restrictionRows descentRows
        representabilityRows provenance ledger endpoint bundle pkg ->
      SheafBHistPointGermLedger site cover objectSection objectRow ->
        SheafBHistPointGermLedger site cover arrowSection arrowRow ->
          hsame cover refinedCover ->
            Cont refinedCover objectSection gluedObject ->
              Cont refinedCover arrowSection gluedArrow ->
                Cont gluedObject gluedArrow gluedLedger ->
                  Cont provenance gluedLedger gluedEndpoint ->
                    PkgSig bundle gluedEndpoint pkg ->
                      StackCarrierPacket site gluedObject gluedArrow transportRows
                          restrictionRows descentRows representabilityRows provenance
                          gluedLedger gluedEndpoint bundle pkg ∧
                        hsame arrowRow gluedArrow := by
  intro packet objectLedger arrowLedger sameCover objectGlue arrowGlue gluedLedgerRow
  intro gluedEndpointRow gluedPkg
  obtain ⟨siteUnary, objectUnary, arrowUnary, transportUnary, restrictionUnary,
    descentUnary, representabilityUnary, provenanceUnary, _ledgerUnary, _endpointUnary,
    _ledgerCont, _endpointCont, _pkgSig⟩ := packet
  have objectReadback :
      SheafBHistPointGermLedger site refinedCover objectSection gluedObject ∧
        hsame objectRow gluedObject :=
    SheafBHistPointGermLedger_restriction_readback objectLedger sameCover objectGlue
  have arrowReadback :
      SheafBHistPointGermLedger site refinedCover arrowSection gluedArrow ∧
        hsame arrowRow gluedArrow :=
    SheafBHistPointGermLedger_restriction_readback arrowLedger sameCover arrowGlue
  have gluedObjectUnary : UnaryHistory gluedObject :=
    unary_transport objectUnary objectReadback.right
  have gluedArrowUnary : UnaryHistory gluedArrow :=
    unary_transport arrowUnary arrowReadback.right
  have gluedLedgerUnary : UnaryHistory gluedLedger :=
    unary_cont_closed gluedObjectUnary gluedArrowUnary gluedLedgerRow
  have gluedEndpointUnary : UnaryHistory gluedEndpoint :=
    unary_cont_closed provenanceUnary gluedLedgerUnary gluedEndpointRow
  exact
    And.intro
      ⟨siteUnary, gluedObjectUnary, gluedArrowUnary, transportUnary, restrictionUnary,
        descentUnary, representabilityUnary, provenanceUnary, gluedLedgerUnary,
        gluedEndpointUnary, gluedLedgerRow, gluedEndpointRow, gluedPkg⟩
      arrowReadback.right

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

theorem StackCarrierPacket_representability_surface [AskSetup] [PackageSetup]
    {schemeSite diagonal atlas overlap cover representability transport endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory schemeSite ->
      UnaryHistory diagonal ->
        UnaryHistory atlas ->
          UnaryHistory overlap ->
            UnaryHistory cover ->
              Cont schemeSite diagonal transport ->
                Cont atlas overlap representability ->
                  Cont transport cover endpoint ->
                    PkgSig bundle endpoint pkg ->
                      UnaryHistory transport ∧ UnaryHistory representability ∧
                        UnaryHistory endpoint ∧ hsame transport (append schemeSite diagonal) ∧
                          hsame representability (append atlas overlap) ∧
                            hsame endpoint (append transport cover) ∧ PkgSig bundle endpoint pkg := by
  intro schemeUnary diagonalUnary atlasUnary overlapUnary coverUnary
  intro siteDiagonalTransport atlasOverlapRepresentability transportCoverEndpoint endpointPkg
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed schemeUnary diagonalUnary siteDiagonalTransport
  have representabilityUnary : UnaryHistory representability :=
    unary_cont_closed atlasUnary overlapUnary atlasOverlapRepresentability
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary coverUnary transportCoverEndpoint
  exact And.intro transportUnary
    (And.intro representabilityUnary
      (And.intro endpointUnary
        (And.intro siteDiagonalTransport
          (And.intro atlasOverlapRepresentability
            (And.intro transportCoverEndpoint endpointPkg)))))

def StackCarrier [AskSetup] [PackageSetup]
    (site presheaf localObj localArrow gluedObj gluedArrow cover restrict provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont localObj restrict gluedObj ∧ Cont localArrow restrict gluedArrow ∧
    Cont site presheaf provenance ∧ Cont provenance cover endpoint ∧
      PkgSig bundle endpoint pkg

theorem StackCarrier_descent_obligation [AskSetup] [PackageSetup]
    {site presheaf localObj localArrow gluedObj gluedArrow cover restrict provenance endpoint
      gluedObj' gluedArrow' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StackCarrier site presheaf localObj localArrow gluedObj gluedArrow cover restrict
        provenance endpoint bundle pkg ->
      Cont localObj restrict gluedObj' ->
        Cont localArrow restrict gluedArrow' ->
          Cont site presheaf provenance' ->
            Cont provenance' cover endpoint' ->
              PkgSig bundle endpoint' pkg ->
                StackCarrier site presheaf localObj localArrow gluedObj' gluedArrow' cover
                    restrict provenance' endpoint' bundle pkg ∧
                  hsame gluedObj gluedObj' ∧ hsame gluedArrow gluedArrow' ∧
                    hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier gluedObjRow' gluedArrowRow' provenanceRow' endpointRow' pkgSig'
  have sameGluedObj : hsame gluedObj gluedObj' :=
    cont_respects_hsame (hsame_refl localObj) (hsame_refl restrict) carrier.left gluedObjRow'
  have sameGluedArrow : hsame gluedArrow gluedArrow' :=
    cont_respects_hsame (hsame_refl localArrow) (hsame_refl restrict)
      carrier.right.left gluedArrowRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl site) (hsame_refl presheaf)
      carrier.right.right.left provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance (hsame_refl cover)
      carrier.right.right.right.left endpointRow'
  have transported :
      StackCarrier site presheaf localObj localArrow gluedObj' gluedArrow' cover restrict
        provenance' endpoint' bundle pkg :=
    ⟨gluedObjRow', gluedArrowRow', provenanceRow', endpointRow', pkgSig'⟩
  exact
    And.intro transported
      (And.intro sameGluedObj
        (And.intro sameGluedArrow
          (And.intro sameProvenance sameEndpoint)))

end BEDC.Derived.StackUp
