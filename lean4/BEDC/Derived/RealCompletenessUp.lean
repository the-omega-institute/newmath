import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RealCompletenessUp finite carrier.
-/

namespace BEDC.Derived.RealCompletenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCompletenessBHistCarrier [AskSetup] [PackageSetup]
    (family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory selector ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem RealCompletenessBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback «seal» transport
        route provenance cert endpoint bundle pkg ->
      UnaryHistory family /\ UnaryHistory modulus /\ UnaryHistory selector /\
        UnaryHistory dyadic /\ UnaryHistory windows /\ UnaryHistory readback /\ UnaryHistory «seal» /\
          UnaryHistory transport /\ UnaryHistory route /\ UnaryHistory provenance /\
            UnaryHistory cert /\ UnaryHistory endpoint /\ Cont transport route endpoint /\
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩ := carrier
  exact ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩

theorem RealCompletenessBHistCarrier_diagonal_witness_schedule [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback «seal» transport route provenance cert endpoint
      diagonal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback «seal» transport
        route provenance cert endpoint bundle pkg →
      Cont selector dyadic diagonal →
        Cont diagonal windows readback →
          Cont readback «seal» endpoint →
            UnaryHistory selector ∧ UnaryHistory dyadic ∧ UnaryHistory diagonal ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory «seal» ∧
                UnaryHistory endpoint ∧ Cont selector dyadic diagonal ∧
                  Cont diagonal windows readback ∧ Cont readback «seal» endpoint ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorDyadic diagonalWindows readbackSeal
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadic
  have readbackUnary' : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  have endpointUnary' : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary' sealUnary readbackSeal
  exact
    ⟨selectorUnary, dyadicUnary, diagonalUnary, windowsUnary, readbackUnary', sealUnary,
      endpointUnary', selectorDyadic, diagonalWindows, readbackSeal, endpointPkg⟩

theorem RealCompletenessBHistCarrier_limit_existence_finite_witness [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      request diagonal witness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      Cont modulus selector request ->
        Cont request dyadic diagonal ->
          Cont diagonal windows witness ->
            Cont witness sealRow endpoint ->
              UnaryHistory modulus ∧ UnaryHistory selector ∧ UnaryHistory request ∧
                UnaryHistory dyadic ∧ UnaryHistory diagonal ∧ UnaryHistory windows ∧
                  UnaryHistory witness ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                    Cont modulus selector request ∧ Cont request dyadic diagonal ∧
                      Cont diagonal windows witness ∧ Cont witness sealRow endpoint ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusSelector requestDyadic diagonalWindows witnessSeal
  obtain ⟨_familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, _readbackUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary, endpointUnary,
    _endpointRoute, endpointPkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed modulusUnary selectorUnary modulusSelector
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed requestUnary dyadicUnary requestDyadic
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  have endpointUnary' : UnaryHistory endpoint :=
    unary_cont_closed witnessUnary sealUnary witnessSeal
  exact
    ⟨modulusUnary, selectorUnary, requestUnary, dyadicUnary, diagonalUnary, windowsUnary,
      witnessUnary, sealUnary, endpointUnary', modulusSelector, requestDyadic, diagonalWindows,
      witnessSeal, endpointPkg⟩

theorem RealCompletenessBHistCarrier_nonescape_boundary [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow
        transport route provenance cert endpoint bundle pkg ->
      Cont sealRow cert publicRead ->
        UnaryHistory publicRead ∧ UnaryHistory sealRow ∧ UnaryHistory cert ∧
          UnaryHistory endpoint ∧ Cont transport route endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier publicReadRow
  obtain ⟨_familyUnary, _modulusUnary, _selectorUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary certUnary publicReadRow
  exact ⟨publicReadUnary, sealUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩

theorem RealCompletenessBHistCarrier_regseq_seal_handoff [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      familyModulus selected readbackRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow
        transport route provenance cert endpoint bundle pkg ->
      Cont family modulus familyModulus ->
        Cont familyModulus selector selected ->
          Cont selected readback readbackRoute ->
            Cont readbackRoute sealRow endpoint ->
              UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory familyModulus ∧
                UnaryHistory selector ∧ UnaryHistory selected ∧ UnaryHistory readback ∧
                  UnaryHistory readbackRoute ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                    Cont family modulus familyModulus ∧
                      Cont familyModulus selector selected ∧
                        Cont selected readback readbackRoute ∧
                          Cont readbackRoute sealRow endpoint ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier familyModulusRoute selectedRoute readbackRouteStep sealRoute
  obtain ⟨familyUnary, modulusUnary, selectorUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _endpointUnary, _endpointRoute, endpointPkg⟩ := carrier
  have familyModulusUnary : UnaryHistory familyModulus :=
    unary_cont_closed familyUnary modulusUnary familyModulusRoute
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed familyModulusUnary selectorUnary selectedRoute
  have readbackRouteUnary : UnaryHistory readbackRoute :=
    unary_cont_closed selectedUnary readbackUnary readbackRouteStep
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackRouteUnary sealUnary sealRoute
  exact
    ⟨familyUnary, modulusUnary, familyModulusUnary, selectorUnary, selectedUnary,
      readbackUnary, readbackRouteUnary, sealUnary, endpointUnary, familyModulusRoute,
      selectedRoute, readbackRouteStep, sealRoute, endpointPkg⟩

theorem RealCompletenessBHistCarrier_tail_budget_stability [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      family' modulus' selector' dyadic' windows' readback' sealRow' diagonal diagonal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      hsame family family' ->
        hsame modulus modulus' ->
          hsame selector selector' ->
            hsame dyadic dyadic' ->
              hsame windows windows' ->
                hsame readback readback' ->
                  hsame sealRow sealRow' ->
                    Cont selector dyadic diagonal ->
                      Cont selector' dyadic' diagonal' ->
                        UnaryHistory modulus' ∧ UnaryHistory selector' ∧
                          UnaryHistory dyadic' ∧ UnaryHistory diagonal' ∧
                            hsame diagonal diagonal' ∧ Cont selector' dyadic' diagonal' ∧
                              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier _sameFamily sameModulus sameSelector sameDyadic _sameWindows _sameReadback
    _sameSeal selectorDyadic selectorDyadic'
  obtain ⟨_familyUnary, modulusUnary, selectorUnary, dyadicUnary, _windowsUnary,
    _readbackUnary, _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _endpointUnary, _endpointRoute, endpointPkg⟩ := carrier
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have selectorUnary' : UnaryHistory selector' :=
    unary_transport selectorUnary sameSelector
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_cont_closed selectorUnary' dyadicUnary' selectorDyadic'
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameSelector sameDyadic selectorDyadic selectorDyadic'
  exact
    ⟨modulusUnary', selectorUnary', dyadicUnary', diagonalUnary', sameDiagonal,
      selectorDyadic', endpointPkg⟩

theorem RealCompletenessBHistCarrier_carrier_transport [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint family' modulus' selector' dyadic' windows' readback' sealRow' transport' route'
      provenance' cert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      hsame family family' ->
        hsame modulus modulus' ->
          hsame selector selector' ->
            hsame dyadic dyadic' ->
              hsame windows windows' ->
                hsame readback readback' ->
                  hsame sealRow sealRow' ->
                    hsame transport transport' ->
                      hsame route route' ->
                        hsame provenance provenance' ->
                          hsame cert cert' ->
                            hsame endpoint endpoint' ->
                              Cont transport' route' endpoint' ->
                                PkgSig bundle endpoint' pkg ->
                                  RealCompletenessBHistCarrier family' modulus' selector'
                                      dyadic' windows' readback' sealRow' transport' route'
                                      provenance' cert' endpoint' bundle pkg ∧
                                    hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier sameFamily sameModulus sameSelector sameDyadic sameWindows sameReadback
    sameSeal sameTransport sameRoute sameProvenance sameCert sameEndpoint endpointRoute'
    endpointPkg'
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    _endpointRoute, _endpointPkg⟩ := carrier
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have selectorUnary' : UnaryHistory selector' :=
    unary_transport selectorUnary sameSelector
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have certUnary' : UnaryHistory cert' :=
    unary_transport certUnary sameCert
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  exact
    ⟨⟨familyUnary', modulusUnary', selectorUnary', dyadicUnary', windowsUnary', readbackUnary',
      sealUnary', transportUnary', routeUnary', provenanceUnary', certUnary', endpointUnary',
      endpointRoute', endpointPkg'⟩, sameEndpoint⟩

theorem RealCompletenessBHistCarrier_candidate_uniqueness_boundary [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      family' modulus' selector' dyadic' windows' readback' sealRow' endpoint' diagonal diagonal'
      candidate candidate' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      hsame selector selector' ->
        hsame dyadic dyadic' ->
          hsame windows windows' ->
            hsame sealRow sealRow' ->
              Cont selector dyadic diagonal ->
                Cont selector' dyadic' diagonal' ->
                  Cont diagonal windows candidate ->
                    Cont diagonal' windows' candidate' ->
                      Cont candidate sealRow endpoint ->
                        Cont candidate' sealRow' endpoint' ->
                          hsame diagonal diagonal' ∧ hsame candidate candidate' ∧
                            hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro _carrier sameSelector sameDyadic sameWindows sameSeal selectorDyadic selectorDyadic'
    diagonalWindows diagonalWindows' candidateSeal candidateSeal'
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameSelector sameDyadic selectorDyadic selectorDyadic'
  have sameCandidate : hsame candidate candidate' :=
    cont_respects_hsame sameDiagonal sameWindows diagonalWindows diagonalWindows'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCandidate sameSeal candidateSeal candidateSeal'
  exact ⟨sameDiagonal, sameCandidate, sameEndpoint⟩

theorem RealCompletenessBHistCarrier_consumer_route_totality [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      request diagonal witness consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      Cont modulus selector request ->
        Cont request dyadic diagonal ->
          Cont diagonal windows witness ->
            Cont witness sealRow endpoint ->
              Cont endpoint cert consumer ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory selector ∧
                    UnaryHistory request ∧ UnaryHistory dyadic ∧ UnaryHistory diagonal ∧
                      UnaryHistory windows ∧ UnaryHistory witness ∧ UnaryHistory sealRow ∧
                        UnaryHistory endpoint ∧ UnaryHistory consumer ∧
                          Cont modulus selector request ∧ Cont request dyadic diagonal ∧
                            Cont diagonal windows witness ∧ Cont witness sealRow endpoint ∧
                              Cont endpoint cert consumer ∧ PkgSig bundle endpoint pkg ∧
                                PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusSelector requestDyadic diagonalWindows witnessSeal endpointConsumer
    consumerPkg
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, _readbackUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary, endpointUnary,
    _endpointRoute, endpointPkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed modulusUnary selectorUnary modulusSelector
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed requestUnary dyadicUnary requestDyadic
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  have endpointUnary' : UnaryHistory endpoint :=
    unary_cont_closed witnessUnary sealUnary witnessSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary' certUnary endpointConsumer
  exact
    ⟨familyUnary, modulusUnary, selectorUnary, requestUnary, dyadicUnary, diagonalUnary,
      windowsUnary, witnessUnary, sealUnary, endpointUnary', consumerUnary, modulusSelector,
      requestDyadic, diagonalWindows, witnessSeal, endpointConsumer, endpointPkg, consumerPkg⟩

theorem RealCompletenessBHistCarrier_witness_extractor_public_obligation [AskSetup]
    [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint witness publicEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg →
      Cont selector dyadic witness →
        Cont witness sealRow publicEndpoint →
          hsame publicEndpoint endpoint →
            PkgSig bundle publicEndpoint pkg →
              UnaryHistory selector ∧ UnaryHistory dyadic ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
                  UnaryHistory publicEndpoint ∧ hsame publicEndpoint endpoint ∧
                    Cont selector dyadic witness ∧ Cont witness sealRow publicEndpoint ∧
                      Cont transport route endpoint ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle publicEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier selectorDyadic witnessSeal publicEndpointEndpoint publicEndpointPkg
  obtain ⟨_familyUnary, _modulusUnary, selectorUnary, dyadicUnary, _windowsUnary,
    _readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadic
  have publicEndpointUnary : UnaryHistory publicEndpoint :=
    unary_cont_closed witnessUnary sealUnary witnessSeal
  exact
    ⟨selectorUnary, dyadicUnary, witnessUnary, sealUnary, certUnary, endpointUnary,
      publicEndpointUnary, publicEndpointEndpoint, selectorDyadic, witnessSeal, endpointRoute,
      endpointPkg, publicEndpointPkg⟩

theorem RealCompletenessBHistCarrier_public_seal_export [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg →
      Cont sealRow cert publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont sealRow cert row ∧ Cont transport route endpoint)
            (fun row : BHist => PkgSig bundle row pkg ∧ Cont transport route endpoint)
            (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg NameCert
  intro carrier publicReadRoute publicReadPkg
  obtain ⟨_familyUnary, _modulusUnary, _selectorUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _endpointUnary, endpointRoute, _endpointPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary certUnary publicReadRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary, publicReadPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨publicReadRoute, endpointRoute⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, endpointRoute⟩
  }

theorem RealCompletenessBHistCarrier_diagonal_limit_candidate [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint request diagonal candidate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      Cont modulus selector request ->
        Cont selector dyadic diagonal ->
          Cont diagonal windows candidate ->
            Cont candidate sealRow endpoint ->
              UnaryHistory sealRow ∧ UnaryHistory endpoint ∧ UnaryHistory modulus ∧
                UnaryHistory selector ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory candidate ∧ Cont modulus selector request ∧
                    Cont selector dyadic diagonal ∧ Cont diagonal windows candidate ∧
                      Cont candidate sealRow endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusSelector selectorDyadic diagonalWindows candidateSeal
  obtain ⟨_familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, _readbackUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _endpointUnary,
    _endpointRoute, endpointPkg⟩ := carrier
  have _requestUnary : UnaryHistory request :=
    unary_cont_closed modulusUnary selectorUnary modulusSelector
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadic
  have candidateUnary : UnaryHistory candidate :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed candidateUnary sealUnary candidateSeal
  exact
    ⟨sealUnary, endpointUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary,
      candidateUnary, modulusSelector, selectorDyadic, diagonalWindows, candidateSeal,
      endpointPkg⟩

theorem RealCompletenessBHistCarrier_modulus_domain_coverage [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert endpoint
      request diagonal selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow transport
        route provenance cert endpoint bundle pkg ->
      Cont modulus selector request ->
        Cont request dyadic diagonal ->
          Cont diagonal windows selectedRead ->
            UnaryHistory modulus ∧ UnaryHistory selector ∧ UnaryHistory request ∧
              UnaryHistory dyadic ∧ UnaryHistory diagonal ∧ UnaryHistory windows ∧
                UnaryHistory selectedRead ∧ Cont modulus selector request ∧
                  Cont request dyadic diagonal ∧ Cont diagonal windows selectedRead ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusSelector requestDyadic diagonalWindows
  obtain ⟨_familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, _readbackUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _endpointUnary,
    _endpointRoute, endpointPkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed modulusUnary selectorUnary modulusSelector
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed requestUnary dyadicUnary requestDyadic
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  exact
    ⟨modulusUnary, selectorUnary, requestUnary, dyadicUnary, diagonalUnary, windowsUnary,
      selectedReadUnary, modulusSelector, requestDyadic, diagonalWindows, endpointPkg⟩

end BEDC.Derived.RealCompletenessUp
