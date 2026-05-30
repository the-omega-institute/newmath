import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_zeckendorf_handoff [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalwordRoute
      zeckendorfRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalwordRoute ->
        Cont normalwordRoute routes zeckendorfRead ->
          PkgSig bundle zeckendorfRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row zeckendorfRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row normalwordRoute ∨ hsame row zeckendorfRead ∨
                    Cont normalwordRoute routes zeckendorfRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle zeckendorfRead pkg)
                hsame ∧
              UnaryHistory normalwordRoute ∧ UnaryHistory zeckendorfRead ∧
                Cont normal continuation normalwordRoute ∧
                  Cont normalwordRoute routes zeckendorfRead ∧
                    PkgSig bundle zeckendorfRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalwordRouteStep zeckendorfStep zeckendorfPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalwordUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed normalUnary continuationUnary normalwordRouteStep
  have zeckendorfUnary : UnaryHistory zeckendorfRead :=
    unary_cont_closed normalwordUnary routesUnary zeckendorfStep
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeckendorfRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normalwordRoute ∨ hsame row zeckendorfRead ∨
              Cont normalwordRoute routes zeckendorfRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle zeckendorfRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro zeckendorfRead ⟨hsame_refl zeckendorfRead, zeckendorfUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inl sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, zeckendorfPkg⟩
  }
  exact
    ⟨cert, normalwordUnary, zeckendorfUnary, normalwordRouteStep, zeckendorfStep,
      zeckendorfPkg⟩

end BEDC.Derived.ZnormalUp
