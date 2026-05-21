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

end BEDC.Derived.BoundedNormalEqualityCheckerUp
