import BEDC.Derived.HaltingObstructionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.HaltingObstructionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingObstructionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {cert input trace self policy transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingObstructionCarrier cert input trace self policy transport route provenance name
        bundle pkg ->
      Cont route policy endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cert ∨ hsame row input ∨ hsame row trace ∨ hsame row self ∨
                  hsame row policy ∨ hsame row route ∨ hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory trace ∧ UnaryHistory self ∧ UnaryHistory policy ∧
              UnaryHistory endpoint ∧ Cont trace self route ∧ Cont route policy endpoint ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier routePolicyEndpoint endpointPkg
  obtain ⟨_certUnary, _inputUnary, traceUnary, selfUnary, policyUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameUnary, _certInputTrace, traceSelfRoute,
    _routePolicyName, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary policyUnary routePolicyEndpoint
  have certSemantic :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cert ∨ hsame row input ∨ hsame row trace ∨ hsame row self ∨
              hsame row policy ∨ hsame row route ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨certSemantic, traceUnary, selfUnary, policyUnary, endpointUnary, traceSelfRoute,
      routePolicyEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingObstructionUp
