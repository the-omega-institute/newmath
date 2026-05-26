import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenCoverRefusalBoundary [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow refusalAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow refusalAudit →
        PkgSig bundle refusalAudit pkg →
          SemanticNameCert
              (fun row : BHist => hsame row refusalAudit ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
                  hsame row refusalAudit)
              (fun row : BHist => hsame row refusalAudit ∧ PkgSig bundle refusalAudit pkg)
              hsame ∧
            UnaryHistory refusalAudit ∧ Cont route nameRow refusalAudit ∧
              PkgSig bundle refusalAudit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeNameRefusal refusalPkg
  obtain ⟨_coverUnary, _windowUnary, _radiusUnary, _meshUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have refusalUnary : UnaryHistory refusalAudit :=
    unary_cont_closed routeUnary nameRowUnary routeNameRefusal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalAudit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row refusalAudit)
          (fun row : BHist => hsame row refusalAudit ∧ PkgSig bundle refusalAudit pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusalAudit ⟨hsame_refl refusalAudit, refusalUnary⟩
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
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, refusalPkg⟩
    }
  exact ⟨cert, refusalUnary, routeNameRefusal, refusalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
