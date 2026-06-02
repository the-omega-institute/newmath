import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProperMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ProperMetricCarrier [AskSetup] [PackageSetup]
    (X B K L T H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
    UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧
      UnaryHistory N ∧ Cont X B K ∧ Cont K L T ∧ Cont T H C ∧
        PkgSig bundle Q pkg

theorem ProperMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X B K L T H C Q N closedCompact locatedComplete : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K closedCompact ->
        Cont K L locatedComplete ->
          PkgSig bundle closedCompact pkg ->
            PkgSig bundle locatedComplete pkg ->
              UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧
                  UnaryHistory N ∧ UnaryHistory closedCompact ∧
                    UnaryHistory locatedComplete ∧ Cont X B K ∧ Cont K L T ∧
                      Cont T H C ∧ Cont B K closedCompact ∧
                        Cont K L locatedComplete ∧ PkgSig bundle Q pkg ∧
                          PkgSig bundle closedCompact pkg ∧
                            PkgSig bundle locatedComplete pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier closedRoute locatedRoute closedPkg locatedPkg
  obtain ⟨XUnary, BUnary, KUnary, LUnary, TUnary, HUnary, CUnary, QUnary, NUnary,
    metricClosedRoute, compactLocatedRoute, handoffRoute, properPkg⟩ := carrier
  have closedUnary : UnaryHistory closedCompact :=
    unary_cont_closed BUnary KUnary closedRoute
  have locatedUnary : UnaryHistory locatedComplete :=
    unary_cont_closed KUnary LUnary locatedRoute
  exact
    ⟨XUnary, BUnary, KUnary, LUnary, TUnary, HUnary, CUnary, QUnary, NUnary,
      closedUnary, locatedUnary, metricClosedRoute, compactLocatedRoute, handoffRoute,
      closedRoute, locatedRoute, properPkg, closedPkg, locatedPkg⟩

theorem ProperMetricCarrier_closed_ball_compactness [AskSetup] [PackageSetup]
    {X B K L T H C Q N compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K compactRead ->
        UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory compactRead ∧
          Cont X B K ∧ Cont B K compactRead ∧ PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier compactRoute
  obtain ⟨XUnary, BUnary, KUnary, _LUnary, _TUnary, _HUnary, _CUnary, _QUnary,
    _NUnary, metricBallRoute, _locatedRoute, _handoffRoute, pkgSig⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed BUnary KUnary compactRoute
  exact ⟨XUnary, BUnary, KUnary, compactReadUnary, metricBallRoute, compactRoute, pkgSig⟩

theorem ProperMetricCarrier_complete_located_handoff [AskSetup] [PackageSetup]
    {X B K L T H C Q N locatedRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont K L locatedRead ->
        Cont L T completeRead ->
          UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
            UnaryHistory T ∧ UnaryHistory locatedRead ∧ UnaryHistory completeRead ∧
              Cont X B K ∧ Cont K L locatedRead ∧ Cont L T completeRead ∧
                hsame locatedRead (append K L) ∧ hsame completeRead (append L T) ∧
                  PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame append
  intro carrier locatedRoute completeRoute
  obtain ⟨XUnary, BUnary, KUnary, LUnary, TUnary, _HUnary, _CUnary, _QUnary, _NUnary,
    metricBallRoute, _locatedStoredRoute, _completeStoredRoute, pkgSig⟩ := carrier
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed KUnary LUnary locatedRoute
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed LUnary TUnary completeRoute
  have locatedReadExact : hsame locatedRead (append K L) := by
    cases locatedRoute
    exact hsame_refl _
  have completeReadExact : hsame completeRead (append L T) := by
    cases completeRoute
    exact hsame_refl _
  exact
    ⟨XUnary, BUnary, KUnary, LUnary, TUnary, locatedReadUnary, completeReadUnary,
      metricBallRoute, locatedRoute, completeRoute, locatedReadExact, completeReadExact,
      pkgSig⟩

theorem ProperMetricCarrier_radius_window_root_soundness [AskSetup] [PackageSetup]
    {X B K L T H C Q N radiusWindow compactRead locatedRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K radiusWindow ->
        Cont radiusWindow K compactRead ->
          Cont K L locatedRead ->
            Cont L T completeRead ->
              PkgSig bundle Q pkg ->
                UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory T ∧ UnaryHistory radiusWindow ∧ UnaryHistory compactRead ∧
                    UnaryHistory locatedRead ∧ UnaryHistory completeRead ∧ Cont X B K ∧
                      Cont B K radiusWindow ∧ Cont radiusWindow K compactRead ∧
                        Cont K L locatedRead ∧ Cont L T completeRead ∧
                          PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier radiusRoute compactRoute locatedRoute completeRoute pkgSig
  obtain ⟨XUnary, BUnary, KUnary, LUnary, TUnary, _HUnary, _CUnary, _QUnary,
    _NUnary, metricBallRoute, _storedLocatedRoute, _storedCompleteRoute,
    _storedPkgSig⟩ := carrier
  have radiusWindowUnary : UnaryHistory radiusWindow :=
    unary_cont_closed BUnary KUnary radiusRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusWindowUnary KUnary compactRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed KUnary LUnary locatedRoute
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed LUnary TUnary completeRoute
  exact
    ⟨XUnary, BUnary, KUnary, LUnary, TUnary, radiusWindowUnary, compactReadUnary,
      locatedReadUnary, completeReadUnary, metricBallRoute, radiusRoute, compactRoute,
      locatedRoute, completeRoute, pkgSig⟩

theorem ProperMetricCarrier_radius_window_nonescape [AskSetup] [PackageSetup]
    {X B K L T H C Q N closedCompact locatedComplete rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K closedCompact ->
        Cont K L locatedComplete ->
          Cont closedCompact locatedComplete rootRead ->
            PkgSig bundle rootRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row B ∨ hsame row K ∨ hsame row L ∨
                      hsame row closedCompact ∨ hsame row locatedComplete ∨
                        hsame row rootRead)
                  (fun row : BHist =>
                    hsame row rootRead ∧ PkgSig bundle Q pkg ∧
                      PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier closedRoute locatedRoute rootRoute rootPkg
  obtain ⟨XUnary, BUnary, KUnary, LUnary, _TUnary, _HUnary, _CUnary, _QUnary, _NUnary,
    _metricClosedRoute, _compactLocatedRoute, _handoffRoute, properPkg⟩ := carrier
  have closedUnary : UnaryHistory closedCompact :=
    unary_cont_closed BUnary KUnary closedRoute
  have locatedUnary : UnaryHistory locatedComplete :=
    unary_cont_closed KUnary LUnary locatedRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed closedUnary locatedUnary rootRoute
  have rootSource :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row B ∨ hsame row K ∨ hsame row L ∨
              hsame row closedCompact ∨ hsame row locatedComplete ∨ hsame row rootRead)
          (fun row : BHist =>
            hsame row rootRead ∧ PkgSig bundle Q pkg ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead rootSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.1,
            unary_transport source.2 same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.1)))))
    ledger_sound := by
      intro row source
      exact ⟨source.1, properPkg, rootPkg⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.ProperMetricUp
