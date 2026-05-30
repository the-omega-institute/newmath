import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricClosedBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricClosedBallCarrier [AskSetup] [PackageSetup]
    (X d c r rho m H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory c ∧ UnaryHistory r ∧
    UnaryHistory rho ∧ UnaryHistory m ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X d H ∧ Cont d c m ∧
        Cont H C N ∧ hsame m (append d c) ∧ PkgSig bundle P pkg

theorem MetricClosedBallCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X d c r rho m H C P N strict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      Cont d c m ->
        Cont rho strict C ->
          SemanticNameCert
            (fun row : BHist =>
              MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ∧ hsame row N)
            (fun row : BHist =>
              MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ∧ hsame row N)
            (fun row : BHist =>
              MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ∧ hsame row N)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro carrier closedMembership strictBoundary
  have accepted : MetricClosedBallCarrier X d c r rho m H C P N bundle pkg := carrier
  obtain ⟨_XUnary, _dUnary, _cUnary, _rUnary, _rhoUnary, _mUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, _sourceRoute, carrierMembership, _nameRoute,
    carrierMembershipSame, _pkgSig⟩ := carrier
  have closedMembershipSame : hsame m (append d c) := closedMembership
  have sameMembershipRows : hsame m (append d c) :=
    hsame_trans carrierMembershipSame (hsame_refl (append d c))
  have strictBoundaryRead : hsame C (append rho strict) := strictBoundary
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N (And.intro accepted (hsame_refl N))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem MetricClosedBallCarrier_metricball_boundary_handoff [AskSetup] [PackageSetup]
    {X d c r rho m H C P N strict openRoute zMembership zNameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      Cont m strict openRoute ->
        hsame openRoute (append m strict) ∧
          (hsame m (BHist.e0 zMembership) -> False) ∧
            (hsame N (BHist.e0 zNameCert) -> False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg UnaryHistory
  intro carrier strictBoundary
  obtain ⟨_XUnary, _dUnary, _cUnary, _rUnary, _rhoUnary, mUnary, _HUnary,
    _CUnary, _PUnary, NUnary, _sourceRoute, _carrierMembership, _nameRoute,
    _carrierMembershipSame, _pkgSig⟩ := carrier
  constructor
  · exact strictBoundary
  constructor
  · intro membershipZero
    exact unary_no_zero_extension (unary_transport mUnary membershipZero)
  · intro nameCertZero
    exact unary_no_zero_extension (unary_transport NUnary nameCertZero)

theorem MetricClosedBallCarrier_obligations [AskSetup] [PackageSetup]
    {X d c r rho m H C P N zX zMembership zNameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory c ∧ UnaryHistory r ∧
        UnaryHistory rho ∧ UnaryHistory m ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont X d H ∧ Cont d c m ∧
            Cont H C N ∧ hsame m (append d c) ∧ PkgSig bundle P pkg ∧
              (hsame X (BHist.e0 zX) -> False) ∧
                (hsame m (BHist.e0 zMembership) -> False) ∧
                  (hsame N (BHist.e0 zNameCert) -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier
  obtain ⟨xUnary, dUnary, cUnary, rUnary, rhoUnary, mUnary, hUnary, cSupportUnary,
    pUnary, nUnary, sourceRoute, membershipRoute, nameRoute, membershipSame, pkgSig⟩ :=
      carrier
  refine ⟨xUnary, dUnary, cUnary, rUnary, rhoUnary, mUnary, hUnary, cSupportUnary,
    pUnary, nUnary, sourceRoute, membershipRoute, nameRoute, membershipSame, pkgSig, ?_,
    ?_, ?_⟩
  · intro sourceZero
    exact unary_no_zero_extension (unary_transport xUnary sourceZero)
  · intro membershipZero
    exact unary_no_zero_extension (unary_transport mUnary membershipZero)
  · intro nameCertZero
    exact unary_no_zero_extension (unary_transport nUnary nameCertZero)

theorem MetricClosedBallCarrier_radius_classifier_stability [AskSetup] [PackageSetup]
    {X d c r rho m H C P N X' d' c' r' rho' m' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      MetricClosedBallCarrier X' d' c' r' rho' m' H' C' P' N' bundle pkg ->
        hsame d d' ->
          hsame c c' ->
            hsame rho rho' ->
              Cont d' c' m' ->
                hsame m m' ∧ UnaryHistory rho ∧ UnaryHistory rho' ∧
                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' sameDistance sameCenter _sameRadiusLedger transportedMembership
  obtain ⟨_XUnary, _dUnary, _cUnary, _rUnary, rhoUnary, _mUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceRoute, membershipRoute, _nameRoute, _membershipSame,
    pkgSig⟩ := carrier
  obtain ⟨_XUnary', _dUnary', _cUnary', _rUnary', rhoUnary', _mUnary', _HUnary',
    _CUnary', _PUnary', _NUnary', _sourceRoute', _membershipRoute', _nameRoute',
    _membershipSame', _pkgSig'⟩ := carrier'
  have membershipStable : hsame m m' :=
    cont_respects_hsame sameDistance sameCenter membershipRoute transportedMembership
  exact ⟨membershipStable, rhoUnary, rhoUnary', pkgSig⟩

theorem MetricClosedBallCarrier_boundary_classifier_transport [AskSetup] [PackageSetup]
    {X d c r rho m H C P N X' d' c' r' rho' m' H' C' P' N' boundary boundary' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      MetricClosedBallCarrier X' d' c' r' rho' m' H' C' P' N' bundle pkg ->
        hsame d d' ->
          hsame c c' ->
            hsame rho rho' ->
              Cont d c m ->
                Cont d' c' m' ->
                  Cont m rho boundary ->
                    Cont m' rho' boundary' ->
                      hsame m m' ∧ hsame boundary boundary' ∧ UnaryHistory boundary ∧
                        UnaryHistory boundary' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' sameDistance sameCenter sameRadius membershipRoute
    transportedMembership boundaryRoute transportedBoundary
  obtain ⟨_XUnary, _dUnary, _cUnary, _rUnary, rhoUnary, mUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceRoute, _carrierMembership, _nameRoute,
    _membershipSame, _pkgSig⟩ := carrier
  obtain ⟨_XUnary', _dUnary', _cUnary', _rUnary', rhoUnary', mUnary', _HUnary',
    _CUnary', _PUnary', _NUnary', _sourceRoute', _carrierMembership',
    _nameRoute', _membershipSame', _pkgSig'⟩ := carrier'
  have membershipStable : hsame m m' :=
    cont_respects_hsame sameDistance sameCenter membershipRoute transportedMembership
  have boundaryStable : hsame boundary boundary' :=
    cont_respects_hsame membershipStable sameRadius boundaryRoute transportedBoundary
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed mUnary rhoUnary boundaryRoute
  have transportedBoundaryUnary : UnaryHistory boundary' :=
    unary_cont_closed mUnary' rhoUnary' transportedBoundary
  exact ⟨membershipStable, boundaryStable, boundaryUnary, transportedBoundaryUnary⟩

theorem MetricClosedBallCarrier_realalgorder_boundary [AskSetup] [PackageSetup]
    {X d c r rho m H C P N boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      Cont d c m ->
        Cont m rho boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory c ∧ UnaryHistory r ∧
              UnaryHistory rho ∧ UnaryHistory m ∧ UnaryHistory boundaryRead ∧
                Cont d c m ∧ Cont m rho boundaryRead ∧ hsame m (append d c) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier membershipRoute boundaryRoute boundaryPkg
  obtain ⟨xUnary, dUnary, cUnary, rUnary, rhoUnary, mUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceRoute, _carrierMembership, _nameRoute,
    membershipSame, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary rhoUnary boundaryRoute
  exact
    ⟨xUnary, dUnary, cUnary, rUnary, rhoUnary, mUnary, boundaryUnary,
      membershipRoute, boundaryRoute, membershipSame, provenancePkg, boundaryPkg⟩

theorem MetricClosedBallCarrier_radius_source_scope [AskSetup] [PackageSetup]
    {X d c r rho m H C P N radiusRead zRadiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      Cont r rho radiusRead ->
        PkgSig bundle radiusRead pkg ->
          UnaryHistory r ∧ UnaryHistory rho ∧ UnaryHistory radiusRead ∧
            Cont r rho radiusRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle radiusRead pkg ∧
                (hsame radiusRead (BHist.e0 zRadiusRead) -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier radiusRoute radiusPkg
  obtain ⟨_xUnary, _dUnary, _cUnary, rUnary, rhoUnary, _mUnary, _hUnary,
    _cSupportUnary, _pUnary, _nUnary, _sourceRoute, _membershipRoute, _nameRoute,
    _membershipSame, provenancePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary rhoUnary radiusRoute
  refine ⟨rUnary, rhoUnary, radiusUnary, radiusRoute, provenancePkg, radiusPkg, ?_⟩
  intro radiusZero
  exact unary_no_zero_extension (unary_transport radiusUnary radiusZero)

theorem MetricClosedBallCarrier_realalgorder_boundary_scope [AskSetup] [PackageSetup]
    {X d c r rho m H C P N boundaryRead replayRead zReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      Cont d c m ->
        Cont m rho boundaryRead ->
          Cont boundaryRead C replayRead ->
            PkgSig bundle replayRead pkg ->
              UnaryHistory m ∧ UnaryHistory rho ∧ UnaryHistory boundaryRead ∧
                UnaryHistory replayRead ∧ hsame m (append d c) ∧
                  Cont m rho boundaryRead ∧ Cont boundaryRead C replayRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg ∧
                      (hsame replayRead (BHist.e0 zReplay) -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier membershipRoute boundaryRoute replayRoute replayPkg
  obtain ⟨_xUnary, _dUnary, _cUnary, _rUnary, rhoUnary, mUnary, _hUnary, cSupportUnary,
    _pUnary, _nUnary, _sourceRoute, _carrierMembership, _nameRoute, membershipSame,
    provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary rhoUnary boundaryRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryUnary cSupportUnary replayRoute
  have membershipScope : hsame m (append d c) :=
    membershipRoute
  refine
    ⟨mUnary, rhoUnary, boundaryUnary, replayUnary, membershipScope, boundaryRoute, replayRoute,
      provenancePkg, replayPkg, ?_⟩
  intro replayZero
  exact unary_no_zero_extension (unary_transport replayUnary replayZero)

end BEDC.Derived.MetricClosedBallUp
