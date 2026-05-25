import BEDC.Derived.ContractionMappingUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContractionMappingCarrier [AskSetup] [PackageSetup]
    (X d T G lambda M I H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory T ∧ UnaryHistory G ∧
    UnaryHistory lambda ∧ UnaryHistory M ∧ UnaryHistory I ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem ContractionMappingCarrier_cauchy_orbit_contractivity [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates replay bound tolerance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      UnaryHistory x0 →
        UnaryHistory iterates →
          Cont x0 iterates replay →
            Cont replay lambda bound →
              Cont bound tolerance I →
                PkgSig bundle replay pkg →
                  UnaryHistory X ∧ UnaryHistory T ∧ UnaryHistory G ∧
                    UnaryHistory lambda ∧ UnaryHistory replay ∧ UnaryHistory bound ∧
                      Cont x0 iterates replay ∧ Cont replay lambda bound ∧
                        Cont bound tolerance I ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier x0Unary iteratesUnary orbitReplay boundReplay tailTolerance replayPkg
  obtain ⟨XUnary, _dUnary, TUnary, GUnary, lambdaUnary, _MUnary, _IUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed x0Unary iteratesUnary orbitReplay
  have boundUnary : UnaryHistory bound :=
    unary_cont_closed replayUnary lambdaUnary boundReplay
  exact
    ⟨XUnary, TUnary, GUnary, lambdaUnary, replayUnary, boundUnary, orbitReplay,
      boundReplay, tailTolerance, provenancePkg, replayPkg⟩

theorem ContractionMappingCarrier_tail_modulus_readiness [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N replay tail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      Cont I M replay →
        Cont replay C tail →
          PkgSig bundle tail pkg →
            UnaryHistory M ∧ UnaryHistory I ∧ UnaryHistory replay ∧ UnaryHistory tail ∧
              Cont I M replay ∧ Cont replay C tail ∧ PkgSig bundle P pkg ∧
                PkgSig bundle tail pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier modulusReplay tailRoute tailPkg
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, MUnary, IUnary, _HUnary,
    CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed IUnary MUnary modulusReplay
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed replayUnary CUnary tailRoute
  exact
    ⟨MUnary, IUnary, replayUnary, tailUnary, modulusReplay, tailRoute, provenancePkg,
      tailPkg⟩

theorem ContractionMappingCarrier_regular_cauchy_modulus_export [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates replay bound tolerance tailBound
      exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      UnaryHistory x0 →
        UnaryHistory iterates →
          Cont x0 iterates replay →
            Cont replay lambda bound →
              Cont bound tolerance I →
                Cont I M tailBound →
                  Cont tailBound H exportRead →
                    PkgSig bundle exportRead pkg →
                      UnaryHistory X ∧ UnaryHistory lambda ∧ UnaryHistory replay ∧
                        UnaryHistory bound ∧ UnaryHistory tailBound ∧
                          UnaryHistory exportRead ∧ Cont x0 iterates replay ∧
                            Cont replay lambda bound ∧ Cont bound tolerance I ∧
                              Cont I M tailBound ∧ Cont tailBound H exportRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier x0Unary iteratesUnary orbitReplay boundReplay toleranceRoute
    tailRoute exportRoute exportPkg
  obtain ⟨XUnary, _dUnary, _TUnary, _GUnary, lambdaUnary, MUnary, IUnary, HUnary,
    _CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed x0Unary iteratesUnary orbitReplay
  have boundUnary : UnaryHistory bound :=
    unary_cont_closed replayUnary lambdaUnary boundReplay
  have tailBoundUnary : UnaryHistory tailBound :=
    unary_cont_closed IUnary MUnary tailRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed tailBoundUnary HUnary exportRoute
  exact
    ⟨XUnary, lambdaUnary, replayUnary, boundUnary, tailBoundUnary, exportReadUnary,
      orbitReplay, boundReplay, toleranceRoute, tailRoute, exportRoute, provenancePkg,
      exportPkg⟩

theorem ContractionMappingCarrier_complete_metric_handoff [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N metricRead graphRead modulusRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      Cont X d metricRead →
        Cont T G graphRead →
          Cont lambda M modulusRead →
            Cont metricRead graphRead completeRead →
              PkgSig bundle completeRead pkg →
                UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory T ∧ UnaryHistory G ∧
                  UnaryHistory lambda ∧ UnaryHistory M ∧ UnaryHistory metricRead ∧
                    UnaryHistory graphRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory completeRead ∧ Cont X d metricRead ∧
                        Cont T G graphRead ∧ Cont lambda M modulusRead ∧
                          Cont metricRead graphRead completeRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle completeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier metricRoute graphRoute modulusRoute completeRoute completePkg
  obtain ⟨XUnary, dUnary, TUnary, GUnary, lambdaUnary, MUnary, _IUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed XUnary dUnary metricRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed TUnary GUnary graphRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed lambdaUnary MUnary modulusRoute
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed metricReadUnary graphReadUnary completeRoute
  exact
    ⟨XUnary, dUnary, TUnary, GUnary, lambdaUnary, MUnary, metricReadUnary,
      graphReadUnary, modulusReadUnary, completeReadUnary, metricRoute, graphRoute,
      modulusRoute, completeRoute, provenancePkg, completePkg⟩

def ContractionMappingOrbitLedger
    (x0 iterates boundPower tolerance adjacentReplay tailReplay : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory x0 ∧ UnaryHistory iterates ∧ UnaryHistory boundPower ∧
    UnaryHistory tolerance ∧ Cont x0 iterates adjacentReplay ∧
      Cont boundPower tolerance tailReplay

theorem ContractionMappingCarrier_orbit_uniqueness_window [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay
      tailReplay x0' iterates' boundPower' tolerance' adjacentReplay' tailReplay'
      commonWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay
        tailReplay →
        ContractionMappingOrbitLedger x0' iterates' boundPower' tolerance'
          adjacentReplay' tailReplay' →
          hsame x0 x0' →
            hsame iterates iterates' →
              Cont x0 iterates commonWindow →
                PkgSig bundle commonWindow pkg →
                  UnaryHistory X ∧ UnaryHistory x0 ∧ UnaryHistory x0' ∧
                    UnaryHistory iterates ∧ UnaryHistory iterates' ∧
                      UnaryHistory commonWindow ∧ hsame x0 x0' ∧
                        hsame iterates iterates' ∧ Cont x0 iterates commonWindow ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle commonWindow pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg PkgSig
  intro carrier orbit orbit' sameStart sameIterates commonRoute commonPkg
  obtain ⟨XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, _MUnary, _IUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  obtain ⟨x0Unary, iteratesUnary, _boundPowerUnary, _toleranceUnary,
    _adjacentRoute, _tailRoute⟩ := orbit
  obtain ⟨x0Unary', iteratesUnary', _boundPowerUnary', _toleranceUnary',
    _adjacentRoute', _tailRoute'⟩ := orbit'
  have commonUnary : UnaryHistory commonWindow :=
    unary_cont_closed x0Unary iteratesUnary commonRoute
  exact
    ⟨XUnary, x0Unary, x0Unary', iteratesUnary, iteratesUnary', commonUnary,
      sameStart, sameIterates, commonRoute, provenancePkg, commonPkg⟩

def ContractionMappingFixedPointReadiness [AskSetup] [PackageSetup]
    (X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay
      tailReplay completeMetricRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg ∧
    ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay tailReplay ∧
      Cont I M completeMetricRead ∧ PkgSig bundle P pkg ∧
        SemanticNameCert
          (fun row : BHist => hsame row completeMetricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row completeMetricRead ∧ Cont x0 iterates adjacentReplay ∧
              Cont boundPower tolerance tailReplay)
          (fun row : BHist => hsame row completeMetricRead ∧ PkgSig bundle P pkg)
          hsame

theorem ContractionMappingCarrier_fixed_point_readiness [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay
      tailReplay completeMetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay tailReplay →
        Cont I M completeMetricRead →
          ContractionMappingFixedPointReadiness X d T G lambda M I H C P N x0 iterates
            boundPower tolerance adjacentReplay tailReplay completeMetricRead bundle pkg ∧
            PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro hCarrier hOrbit completeMetricRoute
  have carrierSurface := hCarrier
  have orbitSurface := hOrbit
  obtain ⟨_x0Unary, _iteratesUnary, _boundPowerUnary, _toleranceUnary,
    adjacentRoute, tailRoute⟩ := hOrbit
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, MUnary, IUnary, _HUnary,
    _CUnary, PUnary, _NUnary, provenancePkg⟩ := hCarrier
  have completeMetricUnary : UnaryHistory completeMetricRead :=
    unary_cont_closed IUnary MUnary completeMetricRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completeMetricRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row completeMetricRead ∧ Cont x0 iterates adjacentReplay ∧
            Cont boundPower tolerance tailReplay)
        (fun row : BHist => hsame row completeMetricRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completeMetricRead ⟨hsame_refl completeMetricRead, completeMetricUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, adjacentRoute, tailRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨⟨carrierSurface, orbitSurface, completeMetricRoute, provenancePkg, cert⟩, provenancePkg⟩

theorem ContractionMappingCarrier_tail_bound_extraction [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay
      tailReplay tailBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay
        tailReplay →
        Cont boundPower tolerance tailBound →
          PkgSig bundle tailBound pkg →
            UnaryHistory lambda ∧ UnaryHistory boundPower ∧ UnaryHistory tolerance ∧
              UnaryHistory tailBound ∧ Cont boundPower tolerance tailBound ∧
                PkgSig bundle P pkg ∧ PkgSig bundle tailBound pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier orbit tailRoute tailPkg
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, lambdaUnary, _MUnary, _IUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  obtain ⟨_x0Unary, _iteratesUnary, boundPowerUnary, toleranceUnary, _adjacentRoute,
    _tailReplayRoute⟩ := orbit
  have tailBoundUnary : UnaryHistory tailBound :=
    unary_cont_closed boundPowerUnary toleranceUnary tailRoute
  exact
    ⟨lambdaUnary, boundPowerUnary, toleranceUnary, tailBoundUnary, tailRoute,
      provenancePkg, tailPkg⟩

end BEDC.Derived.ContractionMappingUp
