import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactRadiusSourceAccountability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow sourceRead compactRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window sourceRead ->
        Cont sourceRead radius compactRead ->
          Cont compactRead route uniformRead ->
            PkgSig bundle uniformRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                      hsame row mesh ∨ hsame row uniformRead)
                  (fun row : BHist =>
                    hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory compactRead ∧
                  UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverWindowSource sourceRadiusCompact compactRouteUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary radiusUnary sourceRadiusCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary routeUnary compactRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact ⟨source.left, uniformPkg⟩
    }
  exact ⟨cert, sourceUnary, compactUnary, uniformUnary⟩

theorem FiniteLebesgueNumberUniformModulusSourceFactorization [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow sourceRead compactRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window sourceRead →
        Cont sourceRead radius compactRead →
          Cont compactRead route uniformRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle uniformRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                        hsame row mesh ∨ hsame row uniformRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                        hsame row uniformRead)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory compactRead ∧
                    UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverWindowSource sourceRadiusCompact compactRouteUniform provenancePkg
    uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _carrierProvenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary radiusUnary sourceRadiusCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary routeUnary compactRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row uniformRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              hsame row uniformRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact ⟨provenancePkg, uniformPkg, source.left⟩
    }
  exact ⟨cert, sourceUnary, compactUnary, uniformUnary⟩

theorem FiniteLebesgueNumberTotalBoundedLedgerReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow sourceRead totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window sourceRead ->
        Cont sourceRead mesh totalRead ->
          PkgSig bundle totalRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row window ∨ hsame row mesh ∨
                    hsame row totalRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧
                    hsame row totalRead)
                hsame ∧
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory mesh ∧
                UnaryHistory sourceRead ∧ UnaryHistory totalRead ∧
                  Cont cover window sourceRead ∧ Cont sourceRead mesh totalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverWindowSource sourceMeshTotal totalPkg
  obtain ⟨coverUnary, windowUnary, _radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have totalUnary : UnaryHistory totalRead :=
    unary_cont_closed sourceUnary meshUnary sourceMeshTotal
  have sourceTotal :
      (fun row : BHist => hsame row totalRead ∧ UnaryHistory row) totalRead := by
    exact ⟨hsame_refl totalRead, totalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row mesh ∨
              hsame row totalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧
              hsame row totalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro totalRead sourceTotal
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
        exact ⟨provenancePkg, totalPkg, source.left⟩
    }
  exact
    ⟨cert, coverUnary, windowUnary, meshUnary, sourceUnary, totalUnary,
      coverWindowSource, sourceMeshTotal, provenancePkg, totalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
