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

theorem LocatedSetCarrier_distance_window_monotonicity [AskSetup] [PackageSetup]
    {X A Q R E T H C P N refinedWindow : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    LocatedSetCarrier X A Q R E T H C P N bundle pkg ->
      Cont Q R refinedWindow ->
        PkgSig bundle refinedWindow pkg ->
          UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory E ∧
            UnaryHistory refinedWindow ∧ Cont X A Q ∧ Cont Q R E ∧
              Cont Q R refinedWindow ∧ Cont E T C ∧ PkgSig bundle P pkg ∧
                PkgSig bundle refinedWindow pkg := by
  -- BEDC touchpoint anchor: LocatedSetCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier refinedRoute refinedPkg
  obtain ⟨_xUnary, _aUnary, qUnary, rUnary, eUnary, _tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, metricRoute, distanceRoute, sealRoute, provenancePkg⟩ :=
      carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed qUnary rUnary refinedRoute
  exact
    ⟨qUnary, rUnary, eUnary, refinedUnary, metricRoute, distanceRoute, refinedRoute,
      sealRoute, provenancePkg, refinedPkg⟩

theorem LocatedSetDistanceLedger_totality [AskSetup] [PackageSetup]
    {X A Q R E T H C P N windowRead sealRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSetCarrier X A Q R E T H C P N bundle pkg ->
      Cont Q R windowRead ->
        Cont windowRead E sealRead ->
          Cont sealRead T handoffRead ->
            PkgSig bundle handoffRead pkg ->
              UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                UnaryHistory handoffRead ∧ Cont X A Q ∧ Cont Q R windowRead ∧
                  Cont windowRead E sealRead ∧ Cont sealRead T handoffRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier windowRoute sealRoute handoffRoute handoffPkg
  obtain ⟨_xUnary, _aUnary, qUnary, rUnary, eUnary, tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, locatedRoute, _distanceRoute, _sealRoute, provenancePkg⟩ :=
      carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed qUnary rUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sealUnary tUnary handoffRoute
  exact
    ⟨windowUnary, sealUnary, handoffUnary, locatedRoute, windowRoute, sealRoute,
      handoffRoute, provenancePkg, handoffPkg⟩

theorem LocatedSetRealDistanceSealExactness [AskSetup] [PackageSetup]
    {X A Q R E T H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSetCarrier X A Q R E T H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row A ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row T)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont E T C)
          hsame ∧
        UnaryHistory E ∧ Cont X A Q ∧ Cont Q R E ∧ Cont E T C ∧
          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier
  obtain ⟨_xUnary, _aUnary, _qUnary, _rUnary, eUnary, _tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, metricRoute, distanceRoute, sealRoute, provenancePkg⟩ :=
      carrier
  have sourceAtE : hsame E E ∧ UnaryHistory E :=
    ⟨hsame_refl E, eUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row A ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row T)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont E T C)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E sourceAtE
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, sealRoute⟩
  }
  exact ⟨cert, eUnary, metricRoute, distanceRoute, sealRoute, provenancePkg⟩

end BEDC.Derived.LocatedSetUp
