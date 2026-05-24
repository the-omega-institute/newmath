import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusMeshStabilityRow [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusRead meshRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius radiusRead →
        Cont radiusRead mesh meshRead →
          Cont meshRead route auditRead →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row radius ∨ hsame row radiusRead ∨ hsame row mesh ∨
                      hsame row meshRead ∨ hsame row auditRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                      hsame row auditRead)
                  hsame ∧
                UnaryHistory radius ∧ UnaryHistory radiusRead ∧ UnaryHistory mesh ∧
                  UnaryHistory meshRead ∧ UnaryHistory auditRead ∧
                    Cont window radius radiusRead ∧ Cont radiusRead mesh meshRead ∧
                      Cont meshRead route auditRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier windowRadiusRead radiusMeshRead meshRouteAudit auditPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed radiusReadUnary meshUnary radiusMeshRead
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed meshReadUnary routeUnary meshRouteAudit
  have sourceAudit :
      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row) auditRead := by
    exact ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row radiusRead ∨ hsame row mesh ∨
              hsame row meshRead ∨ hsame row auditRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              hsame row auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, auditPkg, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, radiusReadUnary, meshUnary, meshReadUnary, auditUnary,
      windowRadiusRead, radiusMeshRead, meshRouteAudit, provenancePkg, auditPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
