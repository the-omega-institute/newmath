import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCarrier_open_phase_root_package [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow openPhase compactRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover mesh openPhase ->
        Cont openPhase route compactRead ->
          PkgSig bundle compactRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row mesh ∨ hsame row openPhase ∨
                    hsame row compactRead)
                (fun row : BHist => PkgSig bundle compactRead pkg ∧ hsame row compactRead)
                hsame ∧
              UnaryHistory cover ∧ UnaryHistory mesh ∧ UnaryHistory openPhase ∧
                UnaryHistory compactRead ∧ Cont cover mesh openPhase ∧
                  Cont openPhase route compactRead ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverMeshOpenPhase openPhaseRouteCompact compactPkg
  obtain ⟨coverUnary, _windowUnary, _radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have openPhaseUnary : UnaryHistory openPhase :=
    unary_cont_closed coverUnary meshUnary coverMeshOpenPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed openPhaseUnary routeUnary openPhaseRouteCompact
  have sourceCompact :
      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row) compactRead := by
    exact ⟨hsame_refl compactRead, compactUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row mesh ∨ hsame row openPhase ∨ hsame row compactRead)
          (fun row : BHist => PkgSig bundle compactRead pkg ∧ hsame row compactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compactRead sourceCompact
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
        exact ⟨compactPkg, source.left⟩
    }
  exact
    ⟨cert, coverUnary, meshUnary, openPhaseUnary, compactUnary, coverMeshOpenPhase,
      openPhaseRouteCompact, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
