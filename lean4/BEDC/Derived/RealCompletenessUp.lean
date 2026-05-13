import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

end BEDC.Derived.RealCompletenessUp
