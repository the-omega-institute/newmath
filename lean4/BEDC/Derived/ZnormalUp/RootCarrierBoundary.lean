import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_carrier_boundary_semantic_namecert [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ZnormalPacket typed fuel terminal normal continuation transports routes provenance
              name bundle pkg ∧
            (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
            Cont continuation transports routes ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro typed
          (And.intro packetWitness (Or.inl (hsame_refl typed)))
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
        intro _row _other sameRows sourceData
        cases sameRows
        exact sourceData
    }
    pattern_sound := by
      intro _row _sourceData
      exact
        ⟨typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
          provenancePkg, namePkg⟩
    ledger_sound := by
      intro _row sourceData
      cases sourceData.right with
      | inl sameTyped =>
          exact ⟨unary_transport typedUnary (hsame_symm sameTyped), provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameFuel =>
              exact ⟨unary_transport fuelUnary (hsame_symm sameFuel), provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameTerminal =>
                  exact
                    ⟨unary_transport terminalUnary (hsame_symm sameTerminal), provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameNormal =>
                      exact
                        ⟨unary_transport normalUnary (hsame_symm sameNormal), provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameContinuation =>
                          exact
                            ⟨unary_transport continuationUnary (hsame_symm sameContinuation),
                              provenancePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameTransports =>
                              exact
                                ⟨unary_transport transportsUnary (hsame_symm sameTransports),
                                  provenancePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameRoutes =>
                                  exact
                                    ⟨unary_transport routesUnary (hsame_symm sameRoutes),
                                      provenancePkg⟩
                              | inr rest =>
                                  cases rest with
                                  | inl sameProvenance =>
                                      exact
                                        ⟨unary_transport provenanceUnary
                                            (hsame_symm sameProvenance),
                                          provenancePkg⟩
                                  | inr sameName =>
                                      exact
                                        ⟨unary_transport nameUnary (hsame_symm sameName),
                                          provenancePkg⟩
  }

end BEDC.Derived.ZnormalUp
