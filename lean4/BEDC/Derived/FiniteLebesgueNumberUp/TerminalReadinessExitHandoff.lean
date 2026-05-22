import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberTerminalReadinessExitHandoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow faceRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window faceRead ->
        Cont faceRead radius endpointRead ->
          PkgSig bundle endpointRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                    hsame row route ∨ hsame row endpointRead)
                (fun row : BHist => hsame row endpointRead ∧ PkgSig bundle endpointRead pkg)
                hsame ∧
              UnaryHistory faceRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverWindowFace faceRadiusEndpoint endpointPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have faceUnary : UnaryHistory faceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowFace
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed faceUnary radiusUnary faceRadiusEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row route ∨ hsame row endpointRead)
          (fun row : BHist => hsame row endpointRead ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }
  exact ⟨cert, faceUnary, endpointUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
