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

end BEDC.Derived.NormedSpaceUp
