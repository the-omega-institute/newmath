import BEDC.Derived.BoundedFunctionFamilyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BoundedFunctionFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedFunctionFamilyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family bound index window evaluation transport route provenance localName
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedFunctionFamilyCarrier family bound index window evaluation transport route
        provenance localName endpoint bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            BoundedFunctionFamilyCarrier family bound index window evaluation transport
              route provenance localName endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row bound ∨ hsame row evaluation ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_familyUnary, _boundUnary, _indexUnary, _windowUnary, _evaluationUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary, _endpointUnary,
    _familyWindowProvenance, _windowEvaluationTransport, _routeProvenanceLocalName,
    _localNamePkg, endpointPkg⟩ := carrier
  have sourceEndpoint :
      (fun row : BHist =>
        BoundedFunctionFamilyCarrier family bound index window evaluation transport route
          provenance localName endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact ⟨carrierWitness, hsame_refl endpoint⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact Or.inr (Or.inr source.right)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }

end BEDC.Derived.BoundedFunctionFamilyUp
