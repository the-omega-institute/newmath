import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPositiveRadiusCompactNetExport [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead
      selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh compactRead →
        Cont compactRead nameRow selectorRead →
          PkgSig bundle selectorRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row radius ∨ hsame row compactRead ∨ hsame row selectorRead)
                (fun row : BHist => hsame row selectorRead ∧ PkgSig bundle selectorRead pkg)
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory compactRead ∧ UnaryHistory selectorRead ∧
                Cont radius mesh compactRead ∧ Cont compactRead nameRow selectorRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshCompact compactNameSelector selectorPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameSelector
  have sourceSelector :
      (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row) selectorRead := by
    exact ⟨hsame_refl selectorRead, selectorUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row compactRead ∨ hsame row selectorRead)
          (fun row : BHist => hsame row selectorRead ∧ PkgSig bundle selectorRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro selectorRead sourceSelector
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, selectorPkg⟩
    }
  exact
    ⟨cert, radiusUnary, compactUnary, selectorUnary, radiusMeshCompact,
      compactNameSelector, provenancePkg, selectorPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
