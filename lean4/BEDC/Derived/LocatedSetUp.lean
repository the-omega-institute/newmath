import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedSetCarrier [AskSetup] [PackageSetup]
    (X A Q R E T H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory Q ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X A Q ∧ Cont Q R E ∧
        Cont E T C ∧ PkgSig bundle P pkg

theorem LocatedSetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X A Q R E T H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSetCarrier X A Q R E T H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedSetCarrier X A Q R E T H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist => hsame row N ∧ Cont X A Q ∧ Cont Q R E ∧ Cont E T C)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  have sourceAtN :
      LocatedSetCarrier X A Q R E T H C P N bundle pkg ∧ hsame N N :=
    ⟨carrier, hsame_refl N⟩
  obtain ⟨_XUnary, _AUnary, _QUnary, _RUnary, _EUnary, _TUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, metricAdmission, distanceReplay, sealReplay, provenance⟩ :=
      carrier
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
      exact ⟨source.right, metricAdmission, distanceReplay, sealReplay⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenance⟩
  }

theorem LocatedSetCarrier_distance_witness_obligation [AskSetup] [PackageSetup]
    {X A Q R E T H C P N witnessRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    LocatedSetCarrier X A Q R E T H C P N bundle pkg ->
      Cont E T witnessRead ->
        PkgSig bundle N pkg ->
          PkgSig bundle witnessRead pkg ->
            UnaryHistory witnessRead ∧ Cont X A Q ∧ Cont Q R E ∧
              Cont E T witnessRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier witnessRoute namePkg witnessPkg
  obtain ⟨_xUnary, _aUnary, _qUnary, _rUnary, eUnary, tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, metricRoute, distanceRoute, _locatedMetricRoute,
    provenancePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed eUnary tUnary witnessRoute
  exact
    ⟨witnessUnary, metricRoute, distanceRoute, witnessRoute, provenancePkg, namePkg,
      witnessPkg⟩

end BEDC.Derived.LocatedSetUp
