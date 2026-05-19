import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
                rightEndpoint sumEndpoint budget readback transports routes provenance localCert
                bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory readback ∧
          Cont sumEndpoint budget readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨leftSourceUnary, rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumEndpointRoute,
    readbackRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumEndpointRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
                rightEndpoint sumEndpoint budget readback transports routes provenance localCert
                bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierWitness⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, leftSourceUnary, rightSourceUnary, readbackUnary, readbackRoute, provenancePkg⟩

end BEDC.Derived.RegularCauchySumUp
