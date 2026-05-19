import BEDC.Derived.AxisZeckendorfCarryBudgetUp

namespace BEDC.Derived.AxisZeckendorfCarryBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCarryBudgetCarrier_full_packet_semantic_namecert [AskSetup]
    [PackageSetup]
    {source target carry normal value boundary transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport
              route provenance name bundle pkg ∧
            (hsame row source ∨ hsame row target ∨ hsame row carry ∨ hsame row normal ∨
              hsame row value ∨ hsame row boundary ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont source target carry ∧ Cont carry normal value ∧
            Cont value boundary transport ∧ Cont transport route provenance ∧
              PkgSig bundle name pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨sourceUnary, targetUnary, carryUnary, normalUnary, valueUnary, boundaryUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, sourceTargetCarry,
    carryNormalValue, valueBoundaryTransport, transportRouteProvenance, namePkg⟩ :=
    carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro source
          (And.intro carrierWitness (Or.inl (hsame_refl source)))
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
        ⟨sourceTargetCarry, carryNormalValue, valueBoundaryTransport,
          transportRouteProvenance, namePkg⟩
    ledger_sound := by
      intro _row sourceData
      cases sourceData.right with
      | inl sameSource =>
          exact ⟨unary_transport sourceUnary (hsame_symm sameSource), namePkg⟩
      | inr rest =>
          cases rest with
          | inl sameTarget =>
              exact ⟨unary_transport targetUnary (hsame_symm sameTarget), namePkg⟩
          | inr rest =>
              cases rest with
              | inl sameCarry =>
                  exact ⟨unary_transport carryUnary (hsame_symm sameCarry), namePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameNormal =>
                      exact ⟨unary_transport normalUnary (hsame_symm sameNormal), namePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameValue =>
                          exact ⟨unary_transport valueUnary (hsame_symm sameValue), namePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameBoundary =>
                              exact
                                ⟨unary_transport boundaryUnary (hsame_symm sameBoundary),
                                  namePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameTransport =>
                                  exact
                                    ⟨unary_transport transportUnary
                                        (hsame_symm sameTransport),
                                      namePkg⟩
                              | inr rest =>
                                  cases rest with
                                  | inl sameRoute =>
                                      exact
                                        ⟨unary_transport routeUnary (hsame_symm sameRoute),
                                          namePkg⟩
                                  | inr rest =>
                                      cases rest with
                                      | inl sameProvenance =>
                                          exact
                                            ⟨unary_transport provenanceUnary
                                                (hsame_symm sameProvenance),
                                              namePkg⟩
                                      | inr sameName =>
                                          exact
                                            ⟨unary_transport nameUnary (hsame_symm sameName),
                                              namePkg⟩
  }

end BEDC.Derived.AxisZeckendorfCarryBudgetUp
