import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_obligation_scope_package [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      Cont endpoint readback realSeal →
        PkgSig bundle realSeal pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row scalar ∨ hsame row source ∨ hsame row window ∨
                  hsame row budget ∨ hsame row readback ∨ hsame row realSeal)
              (fun _row : BHist =>
                Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
                  Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                    Cont scaledEndpoint budget readback ∧ Cont endpoint readback realSeal)
              (fun row : BHist =>
                UnaryHistory row ∧
                  (PkgSig bundle endpoint pkg ∨ PkgSig bundle realSeal pkg))
              hsame ∧
            UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
              UnaryHistory budget ∧ UnaryHistory readback ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointReadbackRealSeal realSealPkg
  obtain ⟨scalarUnary, sourceUnary, windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, endpointUnary, scalarWindow,
    sourceWindow, endpointsScaled, scaledBudgetReadback, _readbackRouteProvenance,
    _provenanceNamecertEndpoint, _sameRowsAppend, endpointPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackRealSeal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row scalar ∨ hsame row source ∨ hsame row window ∨
              hsame row budget ∨ hsame row readback ∨ hsame row realSeal)
          (fun _row : BHist =>
            Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
              Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                Cont scaledEndpoint budget readback ∧ Cont endpoint readback realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle endpoint pkg ∨ PkgSig bundle realSeal pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl realSeal))))))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows'
        exact hsame_symm sameRows'
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows' sourceRow
        cases sourceRow with
        | inl sameScalar =>
            exact Or.inl (hsame_trans (hsame_symm sameRows') sameScalar)
        | inr rest =>
            cases rest with
            | inl sameSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows') sameSource))
            | inr rest =>
                cases rest with
                | inl sameWindow =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows') sameWindow)))
                | inr rest =>
                    cases rest with
                    | inl sameBudget =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows') sameBudget))))
                    | inr rest =>
                        cases rest with
                        | inl sameReadback =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows') sameReadback)))))
                        | inr sameRealSeal =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (hsame_trans (hsame_symm sameRows') sameRealSeal)))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨scalarWindow, sourceWindow, endpointsScaled, scaledBudgetReadback,
          endpointReadbackRealSeal⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl sameScalar =>
          exact ⟨unary_transport scalarUnary (hsame_symm sameScalar), Or.inl endpointPkg⟩
      | inr rest =>
          cases rest with
          | inl sameSource =>
              exact
                ⟨unary_transport sourceUnary (hsame_symm sameSource), Or.inl endpointPkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindow =>
                  exact
                    ⟨unary_transport windowUnary (hsame_symm sameWindow), Or.inl endpointPkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameBudget =>
                      exact
                        ⟨unary_transport budgetUnary (hsame_symm sameBudget),
                          Or.inl endpointPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              Or.inl endpointPkg⟩
                      | inr sameRealSeal =>
                          exact
                            ⟨unary_transport realSealUnary (hsame_symm sameRealSeal),
                              Or.inr realSealPkg⟩
  }
  exact
    ⟨cert, scalarUnary, sourceUnary, windowUnary, budgetUnary, readbackUnary, realSealUnary⟩

end BEDC.Derived.RegularCauchyScaleUp
