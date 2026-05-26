import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedNormalEqualityCheckerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedNormalEqualityCheckerCarrier [AskSetup] [PackageSetup]
    (left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory fuel ∧ UnaryHistory normalLeft ∧
    UnaryHistory normalRight ∧ UnaryHistory equality ∧ UnaryHistory witness ∧
      UnaryHistory closed ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont left fuel normalLeft ∧
          Cont right fuel normalRight ∧ Cont normalLeft normalRight equality ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem BoundedNormalEqualityCheckerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row fuel ∨ hsame row normalLeft ∨
              hsame row normalRight ∨ hsame row equality ∨ hsame row witness ∨
                hsame row closed ∨ hsame row nameCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧ hsame row nameCert)
          hsame ∧
        Cont left fuel normalLeft ∧ Cont right fuel normalRight ∧
          Cont normalLeft normalRight equality ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, _fuelUnary, _normalLeftUnary, _normalRightUnary,
    _equalityUnary, _witnessUnary, _closedUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameCertUnary, leftRoute, rightRoute, equalityRoute, provenancePkg,
    nameCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row fuel ∨ hsame row normalLeft ∨
              hsame row normalRight ∨ hsame row equality ∨ hsame row witness ∨
                hsame row closed ∨ hsame row nameCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧ hsame row nameCert)
          hsame := by
    exact
      { core :=
          { carrier_inhabited := Exists.intro nameCert ⟨hsame_refl nameCert, nameCertUnary⟩
            equiv_refl := by
              intro h _source
              exact hsame_refl h
            equiv_symm := by
              intro h k same
              exact hsame_symm same
            equiv_trans := by
              intro h k r sameHK sameKR
              exact hsame_trans sameHK sameKR
            carrier_respects_equiv := by
              intro h k same source
              exact
                ⟨hsame_trans (hsame_symm same) source.left,
                  unary_transport source.right same⟩ }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
        ledger_sound := by
          intro _row source
          exact ⟨provenancePkg, nameCertPkg, source.left⟩ }
  exact ⟨cert, leftRoute, rightRoute, equalityRoute, nameCertPkg⟩

theorem BoundedNormalEqualityCheckerCarrier_namecert_ledger_read_boundary [AskSetup]
    [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      hsame localRead nameCert ->
        UnaryHistory localRead ->
          (hsame localRead left ∨ hsame localRead right ∨ hsame localRead fuel ∨
              hsame localRead normalLeft ∨ hsame localRead normalRight ∨
                hsame localRead equality ∨ hsame localRead witness ∨ hsame localRead closed ∨
                  hsame localRead nameCert) ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
              hsame localRead nameCert := by
  intro carrier localSame localUnary
  have cert :=
    (BoundedNormalEqualityCheckerCarrier_namecert_obligations carrier).left
  exact
    ⟨cert.pattern_sound ⟨localSame, localUnary⟩,
      cert.ledger_sound ⟨localSame, localUnary⟩⟩

theorem BoundedNormalEqualityCheckerCarrier_finished_soundness_boundary [AskSetup]
    [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert equalityRead finishedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      Cont normalLeft normalRight equalityRead ->
        Cont equalityRead witness finishedRead ->
          hsame equalityRead equality ->
            UnaryHistory normalLeft ∧ UnaryHistory normalRight ∧ UnaryHistory equality ∧
              UnaryHistory equalityRead ∧ UnaryHistory finishedRead ∧
                Cont normalLeft normalRight equality ∧ Cont normalLeft normalRight equalityRead ∧
                  Cont equalityRead witness finishedRead ∧ hsame equalityRead equality ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier equalityReadRoute finishedReadRoute equalityReadSame
  obtain ⟨_leftUnary, _rightUnary, _fuelUnary, normalLeftUnary, normalRightUnary,
    equalityUnary, witnessUnary, _closedUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _leftRoute, _rightRoute, equalityRoute, provenancePkg, _nameCertPkg⟩ :=
    carrier
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed normalLeftUnary normalRightUnary equalityReadRoute
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed equalityReadUnary witnessUnary finishedReadRoute
  exact
    ⟨normalLeftUnary, normalRightUnary, equalityUnary, equalityReadUnary, finishedReadUnary,
      equalityRoute, equalityReadRoute, finishedReadRoute, equalityReadSame, provenancePkg⟩

theorem BoundedNormalEqualityCheckerCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert equalityRead finishedRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      Cont normalLeft normalRight equalityRead ->
        Cont equalityRead witness finishedRead ->
          hsame localRead nameCert ->
            UnaryHistory localRead ->
              UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory fuel ∧
                UnaryHistory normalLeft ∧ UnaryHistory normalRight ∧ UnaryHistory equality ∧
                  UnaryHistory equalityRead ∧ UnaryHistory finishedRead ∧
                    Cont normalLeft normalRight equality ∧
                      Cont normalLeft normalRight equalityRead ∧
                        Cont equalityRead witness finishedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier equalityReadRoute finishedReadRoute _localSame _localUnary
  obtain ⟨leftUnary, rightUnary, fuelUnary, normalLeftUnary, normalRightUnary, equalityUnary,
    witnessUnary, _closedUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _leftRoute, _rightRoute, equalityRoute, provenancePkg, nameCertPkg⟩ :=
      carrier
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed normalLeftUnary normalRightUnary equalityReadRoute
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed equalityReadUnary witnessUnary finishedReadRoute
  exact
    ⟨leftUnary, rightUnary, fuelUnary, normalLeftUnary, normalRightUnary, equalityUnary,
      equalityReadUnary, finishedReadUnary, equalityRoute, equalityReadRoute,
      finishedReadRoute, provenancePkg, nameCertPkg⟩

theorem BoundedNormalEqualityCheckerCarrier_classifier_stability_row [AskSetup]
    [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert leftRead rightRead fuelRead normalLeftRead normalRightRead equalityRead witnessRead
      closedRead nameCertRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      hsame leftRead left ->
        hsame rightRead right ->
          hsame fuelRead fuel ->
            hsame normalLeftRead normalLeft ->
              hsame normalRightRead normalRight ->
                hsame equalityRead equality ->
                  hsame witnessRead witness ->
                    hsame closedRead closed ->
                      hsame nameCertRead nameCert ->
                        UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                          UnaryHistory fuelRead ∧ UnaryHistory normalLeftRead ∧
                            UnaryHistory normalRightRead ∧ UnaryHistory equalityRead ∧
                              UnaryHistory witnessRead ∧ UnaryHistory closedRead ∧
                                UnaryHistory nameCertRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro carrier leftSame rightSame fuelSame normalLeftSame normalRightSame equalitySame
    witnessSame closedSame nameCertSame
  obtain ⟨leftUnary, rightUnary, fuelUnary, normalLeftUnary, normalRightUnary,
    equalityUnary, witnessUnary, closedUnary, _transportUnary, _routeUnary, _provenanceUnary,
    nameCertUnary, _leftRoute, _rightRoute, _equalityRoute, provenancePkg, _nameCertPkg⟩ :=
    carrier
  exact
    ⟨unary_transport leftUnary (hsame_symm leftSame),
      unary_transport rightUnary (hsame_symm rightSame),
      unary_transport fuelUnary (hsame_symm fuelSame),
      unary_transport normalLeftUnary (hsame_symm normalLeftSame),
      unary_transport normalRightUnary (hsame_symm normalRightSame),
      unary_transport equalityUnary (hsame_symm equalitySame),
      unary_transport witnessUnary (hsame_symm witnessSame),
      unary_transport closedUnary (hsame_symm closedSame),
      unary_transport nameCertUnary (hsame_symm nameCertSame), provenancePkg⟩

theorem BoundedNormalEqualityCheckerCarrier_deterministic_normal_form_readback [AskSetup]
    [PackageSetup]
    {left right fuel normalLeft normalRight equality witness closed transport route provenance
      nameCert normalLeftRead normalRightRead equalityRead finishedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedNormalEqualityCheckerCarrier left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert bundle pkg ->
      hsame normalLeftRead normalLeft ->
        hsame normalRightRead normalRight ->
          hsame equalityRead equality ->
            Cont normalLeftRead normalRightRead equalityRead ->
              Cont equalityRead witness finishedRead ->
                UnaryHistory normalLeftRead ∧ UnaryHistory normalRightRead ∧
                  UnaryHistory equalityRead ∧ UnaryHistory finishedRead ∧
                    Cont normalLeftRead normalRightRead equalityRead ∧
                      Cont equalityRead witness finishedRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier normalLeftSame normalRightSame equalitySame equalityReadRoute finishedReadRoute
  obtain ⟨_leftUnary, _rightUnary, _fuelUnary, normalLeftUnary, normalRightUnary,
    _equalityUnary, witnessUnary, _closedUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _leftRoute, _rightRoute, _equalityRoute, provenancePkg, _nameCertPkg⟩ :=
    carrier
  have normalLeftReadUnary : UnaryHistory normalLeftRead :=
    unary_transport normalLeftUnary (hsame_symm normalLeftSame)
  have normalRightReadUnary : UnaryHistory normalRightRead :=
    unary_transport normalRightUnary (hsame_symm normalRightSame)
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed normalLeftReadUnary normalRightReadUnary equalityReadRoute
  have finishedReadUnary : UnaryHistory finishedRead :=
    unary_cont_closed equalityReadUnary witnessUnary finishedReadRoute
  exact
    ⟨normalLeftReadUnary, normalRightReadUnary, equalityReadUnary, finishedReadUnary,
      equalityReadRoute, finishedReadRoute, provenancePkg⟩

end BEDC.Derived.BoundedNormalEqualityCheckerUp
