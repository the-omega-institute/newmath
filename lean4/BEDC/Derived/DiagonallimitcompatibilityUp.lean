import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitCompatibilityCarrier [AskSetup] [PackageSetup]
    (diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
          Cont readback realSeal route ∧ Cont route cert transport ∧
            PkgSig bundle provenance pkg

theorem DiagonalLimitCompatibilityNonEscape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, endpointUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackEndpoint, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibilityCarrier_selector_budget_source_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          PkgSig bundle locked pkg ->
            UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory selector ∧ UnaryHistory locked ∧ Cont diagonal windows selector ∧
                Cont selector readback locked ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, selectorUnary, lockedUnary,
      diagonalWindowsSelector, selectorReadbackLocked, provenancePkg, lockedPkg⟩

theorem DiagonalLimitCompatibilityBudgetSourceLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic source ->
        Cont source windows mesh ->
          Cont mesh triangle locked ->
            PkgSig bundle locked pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory locked ∧
                  Cont diagonal dyadic source ∧ Cont source windows mesh ∧
                    Cont mesh triangle locked ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleLocked lockedPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed meshUnary triangleUnary meshTriangleLocked
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, sourceUnary, meshUnary, lockedUnary,
      diagonalDyadicSource, sourceWindowsMesh, meshTriangleLocked, provenancePkg, lockedPkg⟩

theorem DiagonalLimitCompatibilityCarrier_root_budget_source [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        PkgSig bundle budgetSource pkg ->
          UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory budgetSource ∧
            Cont diagonal dyadic budgetSource ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle budgetSource pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicSource budgetSourcePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  exact
    ⟨diagonalUnary, dyadicUnary, budgetSourceUnary, diagonalDyadicSource, provenancePkg,
      budgetSourcePkg⟩

theorem DiagonalLimitCompatibilitySealBudgetRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          PkgSig bundle sealBudget pkg ->
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
              UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧
                Cont dyadic windows budgetPrefix ∧ Cont budgetPrefix sealRow sealBudget ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealBudget pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow sealBudgetPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  exact
    ⟨dyadicUnary, windowsUnary, budgetPrefixUnary, sealUnary, sealBudgetUnary,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackRealSealRoute, provenancePkg,
      sealBudgetPkg⟩

theorem DiagonalLimitCompatibility_root_route_budget_package [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows budgetPrefix →
      Cont budgetPrefix sealRow sealBudget →
      Cont readback realSeal endpoint →
      PkgSig bundle sealBudget pkg →
      PkgSig bundle endpoint pkg →
        UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
          UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
            UnaryHistory sealBudget ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory endpoint ∧ Cont diagonal triangle sealRow ∧
                Cont dyadic windows budgetPrefix ∧ Cont budgetPrefix sealRow sealBudget ∧
                  Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealBudget pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackEndpoint
    sealBudgetPkg endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, _carrierDyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, budgetPrefixUnary,
      sealBudgetUnary, readbackUnary, realSealUnary, endpointUnary, diagonalTriangleSeal,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackEndpoint, provenancePkg,
      sealBudgetPkg, endpointPkg⟩

theorem DiagonalLimitCompatibility_tolerance_ledger_handoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows readback ->
        Cont readback realSeal endpoint ->
          UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory endpoint ∧ Cont dyadic windows readback ∧
              Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsReadback readbackEndpoint
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _carrierDyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, endpointUnary, dyadicWindowsReadback,
      readbackEndpoint, provenancePkg⟩

theorem DiagonalLimitCompatibility_seal_consumer_factorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
            UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory endpoint ∧ Cont diagonal triangle sealRow ∧
                Cont dyadic windows readback ∧ Cont readback realSeal endpoint ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      endpointUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackEndpoint,
      provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibility_window_route_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                  Cont diagonal windows selector ∧ Cont selector readback locked ∧
                    Cont locked realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, selectorUnary, lockedUnary,
      endpointUnary, diagonalWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibilityRootFormalRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetWindow selectorRoute sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetWindow ->
        Cont budgetWindow windows selectorRoute ->
          Cont selectorRoute readback sealEndpoint ->
            PkgSig bundle sealEndpoint pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory readback ∧ UnaryHistory budgetWindow ∧
                  UnaryHistory selectorRoute ∧ UnaryHistory sealEndpoint ∧
                    Cont diagonal dyadic budgetWindow ∧
                      Cont budgetWindow windows selectorRoute ∧
                        Cont selectorRoute readback sealEndpoint ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicBudgetWindow budgetWindowWindowsSelectorRoute
    selectorRouteReadbackSealEndpoint sealEndpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetWindow
  have selectorRouteUnary : UnaryHistory selectorRoute :=
    unary_cont_closed budgetWindowUnary windowsUnary budgetWindowWindowsSelectorRoute
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed selectorRouteUnary readbackUnary selectorRouteReadbackSealEndpoint
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, budgetWindowUnary,
      selectorRouteUnary, sealEndpointUnary, diagonalDyadicBudgetWindow,
      budgetWindowWindowsSelectorRoute, selectorRouteReadbackSealEndpoint, provenancePkg,
      sealEndpointPkg⟩

theorem DiagonalLimitCompatibilityRootReadbackExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sibling ledger sealOut endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback sibling ->
        Cont sibling dyadic ledger ->
          Cont ledger realSeal sealOut ->
            Cont sealOut sealRow endpoint ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory sibling ∧
                  UnaryHistory dyadic ∧ UnaryHistory ledger ∧ UnaryHistory realSeal ∧
                    UnaryHistory sealOut ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                      Cont windows readback sibling ∧ Cont sibling dyadic ledger ∧
                        Cont ledger realSeal sealOut ∧ Cont sealOut sealRow endpoint ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier windowsReadbackSibling siblingDyadicLedger ledgerRealSealSealOut
    sealOutSealRowEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have siblingUnary : UnaryHistory sibling :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackSibling
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed siblingUnary dyadicUnary siblingDyadicLedger
  have sealOutUnary : UnaryHistory sealOut :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealOut
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealOutUnary sealRowUnary sealOutSealRowEndpoint
  exact
    ⟨windowsUnary, readbackUnary, siblingUnary, dyadicUnary, ledgerUnary, realSealUnary,
      sealOutUnary, sealRowUnary, endpointUnary, windowsReadbackSibling,
      siblingDyadicLedger, ledgerRealSealSealOut, sealOutSealRowEndpoint, provenancePkg,
      endpointPkg⟩

theorem DiagonalLimitCompatibilityBudgetSelectorSupportRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          PkgSig bundle locked pkg ->
            UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
              UnaryHistory cert ∧ Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle locked pkg ∧ Cont diagonal windows selector ∧
                  Cont selector readback locked := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, transportUnary, routeUnary, provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  exact
    ⟨transportUnary, routeUnary, provenanceUnary, certUnary, routeCertTransport, provenancePkg,
      lockedPkg, diagonalWindowsSelector, selectorReadbackLocked⟩

theorem DiagonalLimitCompatibilityRootRouteBudgetPackage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootRoute ->
        PkgSig bundle rootRoute pkg ->
          UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory rootRoute ∧
              Cont diagonal dyadic rootRoute ∧ Cont dyadic windows readback ∧
                Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle rootRoute pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicRoot rootRoutePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootRouteUnary : UnaryHistory rootRoute :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary, rootRouteUnary,
      diagonalDyadicRoot, dyadicWindowsReadback, readbackRealSealRoute, provenancePkg,
      rootRoutePkg⟩

theorem DiagonalLimitCompatibilityRootRequestCoverage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow rootReadback rootSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootBudget ->
        Cont rootBudget windows rootWindow ->
          Cont rootWindow readback rootReadback ->
            Cont rootReadback realSeal rootSeal ->
              PkgSig bundle rootSeal pkg ->
                UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory rootBudget ∧
                    UnaryHistory rootWindow ∧ UnaryHistory rootReadback ∧
                      UnaryHistory rootSeal ∧ Cont diagonal dyadic rootBudget ∧
                        Cont rootBudget windows rootWindow ∧
                          Cont rootWindow readback rootReadback ∧
                            Cont rootReadback realSeal rootSeal ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle rootSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicRootBudget rootBudgetWindowsRootWindow
    rootWindowReadbackRootReadback rootReadbackRealSealRootSeal rootSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRootBudget
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowsUnary rootBudgetWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      rootBudgetUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary,
      diagonalDyadicRootBudget, rootBudgetWindowsRootWindow,
      rootWindowReadbackRootReadback, rootReadbackRealSealRootSeal, provenancePkg,
      rootSealPkg⟩

theorem DiagonalLimitCompatibilityRootSelectorBudgetLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
                  UnaryHistory cert ∧ Cont diagonal windows selector ∧
                    Cont selector readback locked ∧ Cont locked realSeal endpoint ∧
                      Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨selectorUnary, lockedUnary, endpointUnary, transportUnary, routeUnary,
      provenanceUnary, certUnary, diagonalWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, routeCertTransport, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibilityCarrier_root_selector_budget_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector request sealBudget tail sync locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tail ->
          Cont diagonal windows selector ->
            Cont selector request sealBudget ->
              Cont sealBudget tail sync ->
                Cont sync readback locked ->
                  PkgSig bundle locked pkg ->
                    UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory selector ∧
                      UnaryHistory request ∧ UnaryHistory sealBudget ∧ UnaryHistory tail ∧
                        UnaryHistory sync ∧ UnaryHistory readback ∧ UnaryHistory locked ∧
                          Cont diagonal windows selector ∧
                            Cont selector request sealBudget ∧
                              Cont sealBudget tail sync ∧ Cont sync readback locked ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier requestUnary tailUnary diagonalWindowsSelector selectorRequestSealBudget
    sealBudgetTailSync syncReadbackLocked lockedPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed selectorUnary requestUnary selectorRequestSealBudget
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSync
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed syncUnary readbackUnary syncReadbackLocked
  exact
    ⟨diagonalUnary, windowsUnary, selectorUnary, requestUnary, sealBudgetUnary, tailUnary,
      syncUnary, readbackUnary, lockedUnary, diagonalWindowsSelector, selectorRequestSealBudget,
      sealBudgetTailSync, syncReadbackLocked, provenancePkg, lockedPkg⟩

theorem DiagonalLimitCompatibilityCarrier_seal_budget_synchronizer_handoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tail selector compatibility locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tail ->
          UnaryHistory compatibility ->
            Cont sealRow request sealBudget ->
              Cont sealBudget tail selector ->
                Cont selector compatibility locked ->
                  PkgSig bundle locked pkg ->
                    UnaryHistory sealRow ∧ UnaryHistory request ∧ UnaryHistory sealBudget ∧
                      UnaryHistory tail ∧ UnaryHistory selector ∧ UnaryHistory compatibility ∧
                        UnaryHistory locked ∧ Cont sealRow request sealBudget ∧
                          Cont sealBudget tail selector ∧ Cont selector compatibility locked ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier requestUnary tailUnary compatibilityUnary sealRowRequestSealBudget
    sealBudgetTailSelector selectorCompatibilityLocked lockedPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed sealRowUnary requestUnary sealRowRequestSealBudget
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary compatibilityUnary selectorCompatibilityLocked
  exact
    ⟨sealRowUnary, requestUnary, sealBudgetUnary, tailUnary, selectorUnary,
      compatibilityUnary, lockedUnary, sealRowRequestSealBudget, sealBudgetTailSelector,
      selectorCompatibilityLocked, provenancePkg, lockedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
