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

end BEDC.Derived.MetricProjectionUp
