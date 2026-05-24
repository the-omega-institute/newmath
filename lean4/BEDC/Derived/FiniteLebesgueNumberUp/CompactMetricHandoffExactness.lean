import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteLebesgueNumberUp.CompactMetricHandoffExactness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FiniteLebesgueNumberUp

theorem FiniteLebesgueNumberCompactMetricHandoffExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow compactRead →
        PkgSig bundle compactRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                  hsame row mesh ∨ hsame row compactRead)
              (fun row : BHist => hsame row compactRead ∧ PkgSig bundle compactRead pkg)
              hsame ∧
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory compactRead ∧ Cont cover window radius ∧
                Cont radius mesh route ∧ Cont route nameRow compactRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeNameCompact compactPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameCompact
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row compactRead)
          (fun row : BHist => hsame row compactRead ∧ PkgSig bundle compactRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, compactPkg⟩
    }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, compactUnary,
      coverWindowRadius, radiusMeshRoute, routeNameCompact, provenancePkg, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp.CompactMetricHandoffExactness
