import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_namecert_root_obligations [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∨ hsame row normal ∨ hsame row continuation)
        (fun _row : BHist =>
          Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
            PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact {
    core := {
      carrier_inhabited := Exists.intro terminal (Or.inl (hsame_refl terminal))
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
        cases source with
        | inl sameTerminal =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal)
        | inr rest =>
            cases rest with
            | inl sameNormal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal))
            | inr sameContinuation =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) sameContinuation))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨typedFuelTerminal, terminalNormalContinuation, provenancePkg⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameTerminal =>
          exact ⟨unary_transport terminalUnary (hsame_symm sameTerminal), provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameNormal =>
              exact ⟨unary_transport normalUnary (hsame_symm sameNormal), provenancePkg⟩
          | inr sameContinuation =>
              exact
                ⟨unary_transport continuationUnary (hsame_symm sameContinuation),
                  provenancePkg⟩
  }

end BEDC.Derived.ZnormalUp
