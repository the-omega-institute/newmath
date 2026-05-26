import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactConsumerBoundaryRow [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead radiusRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window compactRead ->
        Cont compactRead radius radiusRead ->
          Cont radiusRead mesh boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                      hsame row mesh ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                      hsame row boundaryRead)
                  hsame ∧
                UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                  UnaryHistory mesh ∧ UnaryHistory compactRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory boundaryRead ∧ Cont cover window compactRead ∧
                      Cont compactRead radius radiusRead ∧ Cont radiusRead mesh boundaryRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier coverWindowCompact compactRadiusRead radiusReadMeshBoundary boundaryPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed coverUnary windowUnary coverWindowCompact
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed compactUnary radiusUnary compactRadiusRead
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed radiusReadUnary meshUnary radiusReadMeshBoundary
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row boundaryRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
              hsame row boundaryRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
        exact ⟨provenancePkg, boundaryPkg, source.left⟩
    }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, compactUnary, radiusReadUnary,
      boundaryUnary, coverWindowCompact, compactRadiusRead, radiusReadMeshBoundary,
      provenancePkg, boundaryPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
