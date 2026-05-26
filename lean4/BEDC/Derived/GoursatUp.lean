import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoursatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GoursatCarrier [AskSetup] [PackageSetup]
    (triangle holomorphic edge subdivision mesh cancel replay provenance localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory triangle ∧ UnaryHistory holomorphic ∧ UnaryHistory edge ∧
    UnaryHistory subdivision ∧ UnaryHistory mesh ∧ UnaryHistory cancel ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        UnaryHistory exported ∧ Cont triangle holomorphic edge ∧
          Cont edge subdivision mesh ∧ Cont mesh cancel replay ∧
            Cont replay provenance localName ∧ Cont provenance localName exported ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem GoursatCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {triangle holomorphic edge subdivision mesh cancel replay provenance localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoursatCarrier triangle holomorphic edge subdivision mesh cancel replay provenance localName
        exported bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          GoursatCarrier triangle holomorphic edge subdivision mesh cancel replay provenance
            localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          hsame row localName ∧ Cont triangle holomorphic edge ∧
            Cont edge subdivision mesh ∧ Cont mesh cancel replay)
        (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert AskSetup PackageSetup PkgSig
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrier, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      obtain
        ⟨_triangleUnary, _holomorphicUnary, _edgeUnary, _subdivisionUnary, _meshUnary,
          _cancelUnary, _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary,
          triangleEdgeRoute, subdivisionMeshRoute, replayRoute, _localRoute, _exportedRoute,
          _provenancePkg, _localNamePkg⟩ := source.left
      exact ⟨source.right, triangleEdgeRoute, subdivisionMeshRoute, replayRoute⟩
    ledger_sound := by
      intro _row source
      obtain
        ⟨_triangleUnary, _holomorphicUnary, _edgeUnary, _subdivisionUnary, _meshUnary,
          _cancelUnary, _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary,
          _triangleEdgeRoute, _subdivisionMeshRoute, _replayRoute, _localRoute,
          _exportedRoute, provenancePkg, _localNamePkg⟩ := source.left
      exact ⟨source.right, provenancePkg⟩
  }

theorem GoursatCarrier_triangle_integral_boundary [AskSetup] [PackageSetup]
    {triangle holomorphic edge subdivision mesh cancel replay provenance localName exported
      integralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoursatCarrier triangle holomorphic edge subdivision mesh cancel replay provenance localName
        exported bundle pkg ->
      Cont subdivision mesh integralRead ->
        PkgSig bundle integralRead pkg ->
          UnaryHistory triangle ∧ UnaryHistory holomorphic ∧ UnaryHistory edge ∧
            UnaryHistory subdivision ∧ UnaryHistory mesh ∧ UnaryHistory cancel ∧
              UnaryHistory integralRead ∧ Cont triangle holomorphic edge ∧
                Cont edge subdivision mesh ∧ Cont subdivision mesh integralRead ∧
                  Cont mesh cancel replay ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle integralRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier integralRoute integralPkg
  obtain
    ⟨triangleUnary, holomorphicUnary, edgeUnary, subdivisionUnary, meshUnary, cancelUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, triangleEdgeRoute,
      subdivisionMeshRoute, replayRoute, _localRoute, _exportedRoute, provenancePkg,
      _localNamePkg⟩ := carrier
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed subdivisionUnary meshUnary integralRoute
  exact
    ⟨triangleUnary, holomorphicUnary, edgeUnary, subdivisionUnary, meshUnary, cancelUnary,
      integralUnary, triangleEdgeRoute, subdivisionMeshRoute, integralRoute, replayRoute,
      provenancePkg, integralPkg⟩

end BEDC.Derived.GoursatUp
