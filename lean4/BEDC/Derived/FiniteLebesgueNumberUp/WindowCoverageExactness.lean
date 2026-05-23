import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberWindowCoverageExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow windowRead coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius windowRead ->
        Cont windowRead mesh coverCell ->
          PkgSig bundle coverCell pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row coverCell ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row window ∨ hsame row windowRead ∨ hsame row mesh ∨
                    hsame row coverCell)
                (fun row : BHist => hsame row coverCell ∧ PkgSig bundle coverCell pkg)
                hsame ∧
              UnaryHistory windowRead ∧ UnaryHistory coverCell ∧
                Cont window radius windowRead ∧ Cont windowRead mesh coverCell := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowRadiusRead readMeshCell coverCellPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed windowReadUnary meshUnary readMeshCell
  have sourceCoverCell :
      (fun row : BHist => hsame row coverCell ∧ UnaryHistory row) coverCell := by
    exact ⟨hsame_refl coverCell, coverCellUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverCell ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row windowRead ∨ hsame row mesh ∨
              hsame row coverCell)
          (fun row : BHist => hsame row coverCell ∧ PkgSig bundle coverCell pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro coverCell sourceCoverCell
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, coverCellPkg⟩
    }
  exact ⟨cert, windowReadUnary, coverCellUnary, windowRadiusRead, readMeshCell⟩

end BEDC.Derived.FiniteLebesgueNumberUp
