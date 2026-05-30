import BEDC.Derived.NormedSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NormedSpaceCarrier [AskSetup] [PackageSetup]
    (V R N M Q H T P C : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory M ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧
      UnaryHistory C ∧ Cont V R N ∧ Cont N M Q ∧ Cont Q H T ∧
        PkgSig bundle P pkg ∧ PkgSig bundle C pkg

theorem NormedSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V N metricRead ->
        Cont M Q completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                    hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                      hsame row C ∨ hsame row metricRead ∨ hsame row completionRead)
                (fun row : BHist =>
                  hsame row completionRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier metricRoute completionRoute completionPkg
  obtain ⟨VUnary, _RUnary, NUnary, MUnary, QUnary, _HUnary, _TUnary, _PUnary, _CUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg, _localPkg⟩ :=
      carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed VUnary NUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary QUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row metricRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, metricUnary, completionUnary⟩

theorem NormedSpaceCarrier_metric_nonescape [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V N metricRead ->
        Cont metricRead Q completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                    hsame row Q ∨ hsame row metricRead ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont V N metricRead ∧
                    Cont metricRead Q completionRead ∧ PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier metricRoute completionRoute completionPkg
  obtain ⟨VUnary, _RUnary, NUnary, _MUnary, QUnary, _HUnary, _TUnary, _PUnary, _CUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg, _localPkg⟩ :=
      carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed VUnary NUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary QUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row metricRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N metricRead ∧
              Cont metricRead Q completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, metricRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, metricUnary, completionUnary⟩

def NormedSpaceZeroCarrier (V R N Z T S M C P K : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory Z ∧
    UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory K

theorem NormedSpaceCarrier_zero_exactness [AskSetup] [PackageSetup]
    {V R N Z T S M C P K zeroNorm zeroRoute : BHist} :
    NormedSpaceZeroCarrier V R N Z T S M C P K ->
      Cont Z N zeroNorm ->
        Cont V zeroNorm zeroRoute ->
          UnaryHistory zeroNorm /\ UnaryHistory zeroRoute := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro carrier zeroNormCont zeroRouteCont
  obtain ⟨vUnary, _rUnary, nUnary, zUnary, _tUnary, _sUnary, _mUnary, _cUnary,
    _pUnary, _kUnary⟩ := carrier
  have zeroNormUnary : UnaryHistory zeroNorm :=
    unary_cont_closed zUnary nUnary zeroNormCont
  have zeroRouteUnary : UnaryHistory zeroRoute :=
    unary_cont_closed vUnary zeroNormUnary zeroRouteCont
  exact ⟨zeroNormUnary, zeroRouteUnary⟩

theorem NormedSpaceCarrier_triangle_scalar_compatibility [AskSetup] [PackageSetup]
    {V R N M Q H T P C triangleRead scalarRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V N triangleRead ->
        Cont R N scalarRead ->
          UnaryHistory triangleRead ∧ UnaryHistory scalarRead ∧ Cont V N triangleRead ∧
            Cont R N scalarRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory NormedSpaceCarrier ProbeBundle Pkg
  intro carrier triangleRoute scalarRoute
  obtain ⟨vUnary, rUnary, nUnary, _mUnary, _qUnary, _hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg,
    _localPkg⟩ := carrier
  have triangleUnary : UnaryHistory triangleRead :=
    unary_cont_closed vUnary nUnary triangleRoute
  have scalarUnary : UnaryHistory scalarRead :=
    unary_cont_closed rUnary nUnary scalarRoute
  exact ⟨triangleUnary, scalarUnary, triangleRoute, scalarRoute⟩

theorem NormedSpaceCarrier_cauchy_window_handoff [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory M ∧
                UnaryHistory Q ∧ UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                  UnaryHistory completionRead ∧ Cont V R normRead ∧
                    Cont normRead M metricRead ∧ Cont metricRead Q completionRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier normRoute metricRoute completionRoute completionPkg
  obtain ⟨vUnary, rUnary, nUnary, mUnary, qUnary, _hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  exact
    ⟨vUnary, rUnary, nUnary, mUnary, qUnary, normReadUnary, metricReadUnary,
      completionReadUnary, normRoute, metricRoute, completionRoute, provenancePkg,
      completionPkg⟩

theorem NormedSpaceCarrier_completion_handoff [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont completionRead H structuralRead ->
              PkgSig bundle structuralRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                        hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                          hsame row C ∨ hsame row structuralRead)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle structuralRead pkg ∧
                        hsame row structuralRead)
                    hsame ∧
                  UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier normRoute metricRoute completionRoute structuralRoute structuralPkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, hUnary, _tUnary, _pUnary, _cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg, _localPkg⟩ :=
      carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed completionReadUnary hUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row structuralRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle structuralRead pkg ∧
              hsame row structuralRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro structuralRead ⟨hsame_refl structuralRead, structuralReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, structuralPkg, source.left⟩
  }
  exact ⟨cert, normReadUnary, metricReadUnary, completionReadUnary, structuralReadUnary⟩

theorem NormedSpaceCarrier_root_unblock_source_triad [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead structuralRead namedRead
      zeroNorm zeroRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont completionRead H structuralRead ->
              Cont P C namedRead ->
                Cont N V zeroNorm ->
                  Cont V zeroNorm zeroRoute ->
                    PkgSig bundle structuralRead pkg ->
                      PkgSig bundle namedRead pkg ->
                        UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                          UnaryHistory completionRead ∧ UnaryHistory structuralRead ∧
                            UnaryHistory namedRead ∧ UnaryHistory zeroNorm ∧
                              UnaryHistory zeroRoute ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle structuralRead pkg ∧
                                  PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier normRoute metricRoute completionRoute structuralRoute namedRoute
    zeroNormRoute zeroRouteRoute structuralPkg namedPkg
  obtain ⟨vUnary, rUnary, nUnary, mUnary, qUnary, hUnary, _tUnary, pUnary, cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg, _localPkg⟩ :=
      carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed completionReadUnary hUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary cUnary namedRoute
  have zeroNormUnary : UnaryHistory zeroNorm :=
    unary_cont_closed nUnary vUnary zeroNormRoute
  have zeroRouteUnary : UnaryHistory zeroRoute :=
    unary_cont_closed vUnary zeroNormUnary zeroRouteRoute
  exact
    ⟨normReadUnary, metricReadUnary, completionReadUnary, structuralReadUnary,
      namedReadUnary, zeroNormUnary, zeroRouteUnary, provenancePkg, structuralPkg, namedPkg⟩

theorem NormedSpaceCarrier_completion_facing_nonescape [AskSetup] [PackageSetup]
    {V R N M Q H T P C completionRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont M Q completionRead ->
        Cont completionRead T replayRead ->
          PkgSig bundle replayRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                    hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle replayRead pkg ∧
                    Cont completionRead T replayRead)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory replayRead ∧
                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier completionRoute replayRoute replayPkg
  obtain ⟨_vUnary, _rUnary, _nUnary, mUnary, qUnary, _hUnary, tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary qUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary tUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle replayRead pkg ∧
              Cont completionRead T replayRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayPkg, replayRoute⟩
  }
  exact ⟨cert, completionUnary, replayUnary, provenancePkg⟩

theorem NormedSpaceCarrier_banach_completion_nonescape [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead banachRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont completionRead T banachRead ->
              PkgSig bundle banachRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row banachRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                        hsame row Q ∨ hsame row T ∨ hsame row normRead ∨
                          hsame row metricRead ∨ hsame row completionRead ∨
                            hsame row banachRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont metricRead Q completionRead ∧
                        Cont completionRead T banachRead ∧ PkgSig bundle banachRead pkg)
                    hsame ∧
                  UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory banachRead ∧
                      PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier normRoute metricRoute completionRoute banachRoute banachPkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, _hUnary, tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have banachReadUnary : UnaryHistory banachRead :=
    unary_cont_closed completionReadUnary tUnary banachRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row banachRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row T ∨ hsame row normRead ∨
                hsame row metricRead ∨ hsame row completionRead ∨
                  hsame row banachRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metricRead Q completionRead ∧
              Cont completionRead T banachRead ∧ PkgSig bundle banachRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro banachRead ⟨hsame_refl banachRead, banachReadUnary⟩
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, banachRoute, banachPkg⟩
  }
  exact
    ⟨cert, normReadUnary, metricReadUnary, completionReadUnary, banachReadUnary,
      provenancePkg⟩

theorem NormedSpaceCarrier_vector_transport_obligation [AskSetup] [PackageSetup]
    {V R N M Q H T P C vectorRead transportedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V H vectorRead ->
        Cont vectorRead T transportedRead ->
          Cont transportedRead C namedRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
                        hsame row P ∨ hsame row vectorRead ∨
                          hsame row transportedRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont V H vectorRead ∧
                        Cont vectorRead T transportedRead ∧
                          Cont transportedRead C namedRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory V ∧ UnaryHistory H ∧ UnaryHistory T ∧
                    UnaryHistory C ∧ UnaryHistory vectorRead ∧
                      UnaryHistory transportedRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier vectorRoute transportRoute namedRoute provenancePkg namedPkg
  obtain ⟨vUnary, _rUnary, _nUnary, _mUnary, _qUnary, hUnary, tUnary, _pUnary, cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, _carrierProvenancePkg,
    _localPkg⟩ := carrier
  have vectorReadUnary : UnaryHistory vectorRead :=
    unary_cont_closed vUnary hUnary vectorRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed vectorReadUnary tUnary transportRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed transportedReadUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
              hsame row P ∨ hsame row vectorRead ∨
                hsame row transportedRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V H vectorRead ∧
              Cont vectorRead T transportedRead ∧
                Cont transportedRead C namedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, vectorRoute, transportRoute, namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, vUnary, hUnary, tUnary, cUnary, vectorReadUnary, transportedReadUnary,
      namedReadUnary⟩

end BEDC.Derived.NormedSpaceUp
