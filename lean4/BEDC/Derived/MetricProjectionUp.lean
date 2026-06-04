import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricProjectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricProjectionCarrier [AskSetup] [PackageSetup]
    (H C D I W E T R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory D ∧ UnaryHistory I ∧
    UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont I W E ∧ Cont D I R ∧
        PkgSig bundle P pkg

theorem MetricProjectionCarrier_closest_point_nonescape [AskSetup] [PackageSetup]
    {H C D I W E T R P N endpoint : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont I W endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory I ∧ UnaryHistory W ∧
            UnaryHistory E ∧ UnaryHistory endpoint ∧ Cont I W endpoint ∧
              PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRoute endpointPkg
  obtain ⟨HUnary, CUnary, _DUnary, IUnary, WUnary, EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, _locatedWindow, _distanceReplay, pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed IUnary WUnary endpointRoute
  exact
    ⟨HUnary, CUnary, IUnary, WUnary, EUnary, endpointUnary, endpointRoute, pkgSig,
      endpointPkg⟩

theorem MetricProjectionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {H C D I W E T R P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MetricProjectionCarrier H C D I W E T R P N bundle pkg ∧ hsame row N)
        (fun row : BHist => hsame row N ∧ Cont I W E ∧ Cont D I R)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  have sourceAtN :
      MetricProjectionCarrier H C D I W E T R P N bundle pkg ∧ hsame N N :=
    ⟨carrier, hsame_refl N⟩
  obtain ⟨_HUnary, _CUnary, _DUnary, _IUnary, _WUnary, _EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, locatedWindow, distanceReplay, pkgSig⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceAtN
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, locatedWindow, distanceReplay⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgSig⟩
  }

theorem MetricProjectionCarrier_endpoint_separation [AskSetup] [PackageSetup]
    {H C D I W E T R P N locatedMetric locatedWindow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg →
      Cont D I locatedMetric →
        Cont locatedMetric W locatedWindow →
          Cont locatedWindow E endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory D ∧ UnaryHistory I ∧ UnaryHistory W ∧ UnaryHistory E ∧
                UnaryHistory locatedMetric ∧ UnaryHistory locatedWindow ∧
                  UnaryHistory endpoint ∧ Cont D I locatedMetric ∧
                    Cont locatedMetric W locatedWindow ∧ Cont locatedWindow E endpoint ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier locatedMetricRoute locatedWindowRoute endpointRoute endpointPkg
  obtain ⟨_HUnary, _CUnary, DUnary, IUnary, WUnary, EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, _windowRoute, _replayRoute, provenancePkg⟩ := carrier
  have locatedMetricUnary : UnaryHistory locatedMetric :=
    unary_cont_closed DUnary IUnary locatedMetricRoute
  have locatedWindowUnary : UnaryHistory locatedWindow :=
    unary_cont_closed locatedMetricUnary WUnary locatedWindowRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed locatedWindowUnary EUnary endpointRoute
  exact
    ⟨DUnary, IUnary, WUnary, EUnary, locatedMetricUnary, locatedWindowUnary,
      endpointUnary, locatedMetricRoute, locatedWindowRoute, endpointRoute,
      provenancePkg, endpointPkg⟩

theorem MetricProjectionCarrier_locatedset_endpoint_separation [AskSetup] [PackageSetup]
    {H C D I W E T R P N locatedEndpoint projectionEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont D I locatedEndpoint ->
        Cont I W projectionEndpoint ->
          PkgSig bundle projectionEndpoint pkg ->
            UnaryHistory D ∧ UnaryHistory I ∧ UnaryHistory W ∧
              UnaryHistory locatedEndpoint ∧ UnaryHistory projectionEndpoint ∧
                Cont D I locatedEndpoint ∧ Cont I W projectionEndpoint ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle projectionEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier locatedRoute projectionRoute projectionPkg
  obtain ⟨_HUnary, _CUnary, DUnary, IUnary, WUnary, _EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, _windowRoute, _distanceRoute, pkgSig⟩ := carrier
  have locatedUnary : UnaryHistory locatedEndpoint :=
    unary_cont_closed DUnary IUnary locatedRoute
  have projectionUnary : UnaryHistory projectionEndpoint :=
    unary_cont_closed IUnary WUnary projectionRoute
  exact
    ⟨DUnary, IUnary, WUnary, locatedUnary, projectionUnary, locatedRoute,
      projectionRoute, pkgSig, projectionPkg⟩

theorem MetricProjectionCarrier_obligation_carrier_stability [AskSetup] [PackageSetup]
    {H C D I W E T R P N H' C' D' I' W' E' T' R' P' N' read read' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      hsame H H' ->
        hsame C C' ->
          hsame D D' ->
            hsame I I' ->
              hsame W W' ->
                hsame E E' ->
                  hsame T T' ->
                    hsame R R' ->
                      hsame P P' ->
                        hsame N N' ->
                          Cont I W read ->
                            hsame read read' ->
                              PkgSig bundle read' pkg ->
                                UnaryHistory H' ∧ UnaryHistory C' ∧
                                  UnaryHistory D' ∧ UnaryHistory I' ∧
                                    UnaryHistory W' ∧ UnaryHistory E' ∧
                                      UnaryHistory T' ∧ UnaryHistory R' ∧
                                        UnaryHistory P' ∧ UnaryHistory N' ∧
                                          UnaryHistory read' ∧ Cont I W read ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle read' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameH sameC sameD sameI sameW sameE sameT sameR sameP sameN
    readRoute sameRead readPkg
  obtain ⟨HUnary, CUnary, DUnary, IUnary, WUnary, EUnary, TUnary, RUnary, PUnary,
    NUnary, _windowRoute, _distanceRoute, provenance⟩ := carrier
  have HUnary' : UnaryHistory H' := unary_transport HUnary sameH
  have CUnary' : UnaryHistory C' := unary_transport CUnary sameC
  have DUnary' : UnaryHistory D' := unary_transport DUnary sameD
  have IUnary' : UnaryHistory I' := unary_transport IUnary sameI
  have WUnary' : UnaryHistory W' := unary_transport WUnary sameW
  have EUnary' : UnaryHistory E' := unary_transport EUnary sameE
  have TUnary' : UnaryHistory T' := unary_transport TUnary sameT
  have RUnary' : UnaryHistory R' := unary_transport RUnary sameR
  have PUnary' : UnaryHistory P' := unary_transport PUnary sameP
  have NUnary' : UnaryHistory N' := unary_transport NUnary sameN
  have readUnary : UnaryHistory read := unary_cont_closed IUnary WUnary readRoute
  have readUnary' : UnaryHistory read' := unary_transport readUnary sameRead
  exact
    ⟨HUnary', CUnary', DUnary', IUnary', WUnary', EUnary', TUnary', RUnary',
      PUnary', NUnary', readUnary', readRoute, provenance, readPkg⟩

end BEDC.Derived.MetricProjectionUp
