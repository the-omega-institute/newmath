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

theorem MetricProjectionCarrierEndpointAdmissionCertificate [AskSetup] [PackageSetup]
    {H C D I W E T R P N transportRead replayRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont E T transportRead ->
        Cont transportRead R replayRead ->
          Cont replayRead N consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    MetricProjectionCarrier H C D I W E T R P N bundle pkg ∧
                      hsame row N)
                  (fun row : BHist => hsame row N ∧ Cont I W E ∧ Cont D I R)
                  (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                  hsame ∧
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row H ∨ hsame row C ∨ hsame row D ∨ hsame row I ∨
                        hsame row W ∨ hsame row E ∨ hsame row T ∨ hsame row R ∨
                          hsame row P ∨ hsame row N ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont I W E ∧ Cont E T transportRead ∧
                        Cont transportRead R replayRead ∧
                          Cont replayRead N consumerRead ∧ Cont D I R ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg)
                    hsame ∧
                  UnaryHistory transportRead ∧ UnaryHistory replayRead ∧
                    UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier endpointTransport transportReplay replayConsumer consumerPkg
  have rootCert :=
    MetricProjectionCarrier_namecert_obligations
      (H := H) (C := C) (D := D) (I := I) (W := W) (E := E) (T := T)
      (R := R) (P := P) (N := N) (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨_HUnary, _CUnary, _DUnary, IUnary, WUnary, EUnary, TUnary, RUnary,
    _PUnary, NUnary, locatedWindow, distanceReplay, pkgSig⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed EUnary TUnary endpointTransport
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary RUnary transportReplay
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed replayUnary NUnary replayConsumer
  have consumerCert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row C ∨ hsame row D ∨ hsame row I ∨
              hsame row W ∨ hsame row E ∨ hsame row T ∨ hsame row R ∨
                hsame row P ∨ hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I W E ∧ Cont E T transportRead ∧
              Cont transportRead R replayRead ∧ Cont replayRead N consumerRead ∧
                Cont D I R ∧ PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, locatedWindow, endpointTransport, transportReplay,
          replayConsumer, distanceReplay, pkgSig, consumerPkg⟩
  }
  exact ⟨rootCert, consumerCert, transportUnary, replayUnary, consumerUnary⟩

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

theorem MetricProjectionLocatedInfimumReplayObligation [AskSetup] [PackageSetup]
    {H C D I W E T R P N hilbertConvex distanceInfimum windowEndpoint replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont H C hilbertConvex ->
        Cont D I distanceInfimum ->
          Cont I W windowEndpoint ->
            Cont windowEndpoint E replayRead ->
              PkgSig bundle replayRead pkg ->
                UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory D ∧ UnaryHistory I ∧
                  UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory hilbertConvex ∧
                    UnaryHistory distanceInfimum ∧ UnaryHistory windowEndpoint ∧
                      UnaryHistory replayRead ∧ Cont H C hilbertConvex ∧
                        Cont D I distanceInfimum ∧ Cont I W windowEndpoint ∧
                          Cont windowEndpoint E replayRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier hilbertRoute distanceRoute windowRoute replayRoute replayPkg
  obtain ⟨HUnary, CUnary, DUnary, IUnary, WUnary, EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, _storedWindowRoute, _storedDistanceRoute, provenancePkg⟩ :=
    carrier
  have hilbertConvexUnary : UnaryHistory hilbertConvex :=
    unary_cont_closed HUnary CUnary hilbertRoute
  have distanceInfimumUnary : UnaryHistory distanceInfimum :=
    unary_cont_closed DUnary IUnary distanceRoute
  have windowEndpointUnary : UnaryHistory windowEndpoint :=
    unary_cont_closed IUnary WUnary windowRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed windowEndpointUnary EUnary replayRoute
  exact
    ⟨HUnary, CUnary, DUnary, IUnary, WUnary, EUnary, hilbertConvexUnary,
      distanceInfimumUnary, windowEndpointUnary, replayReadUnary, hilbertRoute,
      distanceRoute, windowRoute, replayRoute, provenancePkg, replayPkg⟩

theorem MetricProjectionCarrier_public_projection_certificate [AskSetup] [PackageSetup]
    {H C D I W E T R P N locatedEndpoint projectionEndpoint endpointRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg →
      Cont D I locatedEndpoint →
        Cont I W projectionEndpoint →
          Cont projectionEndpoint E endpointRead →
            Cont endpointRead N publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row H ∨ hsame row C ∨ hsame row D ∨ hsame row I ∨
                        hsame row W ∨ hsame row E ∨ hsame row T ∨ hsame row R ∨
                          hsame row P ∨ hsame row N ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D I locatedEndpoint ∧
                        Cont I W projectionEndpoint ∧
                          Cont projectionEndpoint E endpointRead ∧
                            Cont endpointRead N publicRead ∧
                              PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory locatedEndpoint ∧ UnaryHistory projectionEndpoint ∧
                    UnaryHistory endpointRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier locatedRoute projectionRoute endpointRoute publicRoute publicPkg
  obtain ⟨_HUnary, _CUnary, DUnary, IUnary, WUnary, EUnary, _TUnary, _RUnary,
    _PUnary, NUnary, _windowRoute, _distanceRoute, _provenancePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedEndpoint :=
    unary_cont_closed DUnary IUnary locatedRoute
  have projectionUnary : UnaryHistory projectionEndpoint :=
    unary_cont_closed IUnary WUnary projectionRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed projectionUnary EUnary endpointRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary NUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row W ∨
              hsame row E ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D I locatedEndpoint ∧
              Cont I W projectionEndpoint ∧ Cont projectionEndpoint E endpointRead ∧
                Cont endpointRead N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, locatedRoute, projectionRoute, endpointRoute, publicRoute,
          publicPkg⟩
  }
  exact ⟨cert, locatedUnary, projectionUnary, endpointUnary, publicUnary⟩

theorem MetricProjectionCarrier_public_projection_separated_certificate
    [AskSetup] [PackageSetup]
    {H C D I W E T R P N locatedEndpoint projectionEndpoint endpointRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont D I locatedEndpoint ->
        Cont I W projectionEndpoint ->
          Cont projectionEndpoint E endpointRead ->
            Cont endpointRead N publicRead ->
              PkgSig bundle projectionEndpoint pkg ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row H ∨ hsame row C ∨ hsame row D ∨ hsame row I ∨
                          hsame row W ∨ hsame row E ∨ hsame row T ∨ hsame row R ∨
                            hsame row P ∨ hsame row N ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D I locatedEndpoint ∧
                          Cont I W projectionEndpoint ∧
                            Cont projectionEndpoint E endpointRead ∧
                              Cont endpointRead N publicRead ∧
                                PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory D ∧ UnaryHistory I ∧ UnaryHistory W ∧
                      UnaryHistory locatedEndpoint ∧ UnaryHistory projectionEndpoint ∧
                        UnaryHistory endpointRead ∧ UnaryHistory publicRead ∧
                          Cont D I locatedEndpoint ∧ Cont I W projectionEndpoint ∧
                            Cont projectionEndpoint E endpointRead ∧
                              Cont endpointRead N publicRead ∧
                                PkgSig bundle P pkg ∧
                                  PkgSig bundle projectionEndpoint pkg ∧
                                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier locatedRoute projectionRoute endpointRoute publicRoute projectionPkg
    publicPkg
  have separated :=
    MetricProjectionCarrier_locatedset_endpoint_separation
      (H := H) (C := C) (D := D) (I := I) (W := W) (E := E) (T := T)
      (R := R) (P := P) (N := N) (bundle := bundle) (pkg := pkg)
      carrier locatedRoute projectionRoute projectionPkg
  have publicCert :=
    MetricProjectionCarrier_public_projection_certificate
      (H := H) (C := C) (D := D) (I := I) (W := W) (E := E) (T := T)
      (R := R) (P := P) (N := N) (bundle := bundle) (pkg := pkg)
      carrier locatedRoute projectionRoute endpointRoute publicRoute publicPkg
  obtain
    ⟨DUnary, IUnary, WUnary, locatedUnary, projectionUnary, locatedRoute',
      projectionRoute', provenancePkg, projectionPkg'⟩ := separated
  obtain ⟨cert, _locatedUnaryPublic, _projectionUnaryPublic, endpointUnary, publicUnary⟩ :=
    publicCert
  exact
    ⟨cert, DUnary, IUnary, WUnary, locatedUnary, projectionUnary, endpointUnary,
      publicUnary, locatedRoute', projectionRoute', endpointRoute, publicRoute,
      provenancePkg, projectionPkg', publicPkg⟩

end BEDC.Derived.MetricProjectionUp
