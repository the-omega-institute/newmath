import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_scope_triad [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name typedRoute
      normalRoute continuationRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel typedRoute →
        Cont normal continuation normalRoute →
          Cont terminal normal continuationRoute →
            PkgSig bundle typedRoute pkg →
              PkgSig bundle normalRoute pkg →
                PkgSig bundle continuationRoute pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row typedRoute ∨ hsame row normalRoute ∨
                        hsame row continuationRoute)
                    (fun _row : BHist =>
                      Cont typed fuel typedRoute ∧ Cont normal continuation normalRoute ∧
                        Cont terminal normal continuationRoute)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        (PkgSig bundle typedRoute pkg ∨ PkgSig bundle normalRoute pkg ∨
                          PkgSig bundle continuationRoute pkg))
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet typedFuelTypedRoute normalContinuationNormalRoute
    terminalNormalContinuationRoute typedRoutePkg normalRoutePkg continuationRoutePkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have typedRouteUnary : UnaryHistory typedRoute :=
    unary_cont_closed typedUnary fuelUnary typedFuelTypedRoute
  have normalRouteUnary : UnaryHistory normalRoute :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalRoute
  have continuationRouteUnary : UnaryHistory continuationRoute :=
    unary_cont_closed terminalUnary normalUnary terminalNormalContinuationRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro typedRoute (Or.inl (hsame_refl typedRoute))
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
        intro row row' sameRows sourceRow
        cases sourceRow with
        | inl sameTyped =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTyped)
        | inr rest =>
            cases rest with
            | inl sameNormal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal))
            | inr sameContinuation =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) sameContinuation))
    }
    pattern_sound := by
      intro _row _sourceRow
      exact
        ⟨typedFuelTypedRoute, normalContinuationNormalRoute,
          terminalNormalContinuationRoute⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow with
      | inl sameTyped =>
          exact
            ⟨unary_transport typedRouteUnary (hsame_symm sameTyped),
              Or.inl typedRoutePkg⟩
      | inr rest =>
          cases rest with
          | inl sameNormal =>
              exact
                ⟨unary_transport normalRouteUnary (hsame_symm sameNormal),
                  Or.inr (Or.inl normalRoutePkg)⟩
          | inr sameContinuation =>
              exact
                ⟨unary_transport continuationRouteUnary (hsame_symm sameContinuation),
                  Or.inr (Or.inr continuationRoutePkg)⟩
  }

end BEDC.Derived.ZnormalUp
