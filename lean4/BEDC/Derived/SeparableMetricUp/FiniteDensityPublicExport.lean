import BEDC.Derived.SeparableMetricUp.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricCarrier_finite_density_public_export [AskSetup] [PackageSetup]
    {metric dense windows tolerance readback sealRow transports routes provenance localCert
      completeRead polishRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableMetricCarrier metric dense windows tolerance readback sealRow transports routes
        provenance localCert bundle pkg ->
      Cont readback sealRow completeRead ->
        Cont completeRead localCert polishRead ->
          PkgSig bundle polishRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row completeRead ∨ hsame row polishRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row dense ∨ hsame row windows ∨
                    hsame row tolerance ∨ hsame row readback ∨ hsame row sealRow ∨
                      hsame row completeRead ∨ hsame row polishRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle polishRead pkg)
                hsame ∧
              UnaryHistory completeRead ∧ UnaryHistory polishRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completeRoute polishRoute polishPkg
  obtain ⟨_metricUnary, _denseUnary, _windowsUnary, _toleranceUnary, readbackUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, localCertUnary,
      _denseWindowRoute, _toleranceReadbackRoute, _sealRoute, provenancePkg,
        _localCert⟩ := carrier
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed readbackUnary sealRowUnary completeRoute
  have polishUnary : UnaryHistory polishRead :=
    unary_cont_closed completeUnary localCertUnary polishRoute
  have sourceComplete :
      (fun row : BHist =>
        (hsame row completeRead ∨ hsame row polishRead) ∧ UnaryHistory row) completeRead := by
    exact ⟨Or.inl (hsame_refl completeRead), completeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completeRead ∨ hsame row polishRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row dense ∨ hsame row windows ∨
              hsame row tolerance ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row completeRead ∨ hsame row polishRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle polishRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completeRead sourceComplete
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
        cases source.left with
        | inl sameComplete =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameComplete),
                unary_transport source.right sameRows⟩
        | inr samePolish =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) samePolish),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameComplete =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inl sameComplete))))))
      | inr samePolish =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr samePolish))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, polishPkg⟩
  }
  exact ⟨cert, completeUnary, polishUnary⟩

end BEDC.Derived.SeparableMetricUp
