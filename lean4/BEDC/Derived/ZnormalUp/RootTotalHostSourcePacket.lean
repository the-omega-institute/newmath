import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_total_host_source_packet [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name rootSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont routes name rootSource →
        PkgSig bundle rootSource pkg →
          SemanticNameCert
              (fun row : BHist =>
                ZnormalPacket typed fuel terminal normal continuation transports routes provenance
                  name bundle pkg ∧
                (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                      hsame row rootSource))
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                      hsame row rootSource)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
                UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                  UnaryHistory rootSource ∧ Cont typed fuel terminal ∧
                    Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                      Cont routes name rootSource ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle rootSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet routesNameRootSource rootSourcePkg
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have rootSourceUnary : UnaryHistory rootSource :=
    unary_cont_closed routesUnary nameUnary routesNameRootSource
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
              bundle pkg ∧
            (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row rootSource))
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row rootSource)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro typed
            ⟨packetWitness, Or.inl (hsame_refl typed)⟩
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
          intro _row _row' sameRows source
          constructor
          · exact source.left
          · cases source.right with
            | inl sameTyped =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameTyped)
            | inr rest =>
                cases rest with
                | inl sameFuel =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameFuel))
                | inr rest =>
                    cases rest with
                    | inl sameTerminal =>
                        exact Or.inr
                          (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameTerminal)))
                    | inr rest =>
                        cases rest with
                        | inl sameNormal =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameNormal))))
                        | inr rest =>
                            cases rest with
                            | inl sameContinuation =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameContinuation)))))
                            | inr rest =>
                                cases rest with
                                | inl sameTransports =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameTransports))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameRoutes =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameRoutes)))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameProvenance =>
                                            exact Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameProvenance))))))))
                                        | inr rest =>
                                            cases rest with
                                            | inl sameName =>
                                                exact Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameName)))))))))
                                            | inr sameRoot =>
                                                exact Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (hsame_trans
                                                                    (hsame_symm sameRows)
                                                                    sameRoot)))))))))
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro row source
        cases source.right with
        | inl sameTyped =>
            exact
              ⟨unary_transport typedUnary (hsame_symm sameTyped), provenancePkg⟩
        | inr rest =>
            cases rest with
            | inl sameFuel =>
                exact
                  ⟨unary_transport fuelUnary (hsame_symm sameFuel), provenancePkg⟩
            | inr rest =>
                cases rest with
                | inl sameTerminal =>
                    exact
                      ⟨unary_transport terminalUnary (hsame_symm sameTerminal),
                        provenancePkg⟩
                | inr rest =>
                    cases rest with
                    | inl sameNormal =>
                        exact
                          ⟨unary_transport normalUnary (hsame_symm sameNormal),
                            provenancePkg⟩
                    | inr rest =>
                        cases rest with
                        | inl sameContinuation =>
                            exact
                              ⟨unary_transport continuationUnary
                                (hsame_symm sameContinuation), provenancePkg⟩
                        | inr rest =>
                            cases rest with
                            | inl sameTransports =>
                                exact
                                  ⟨unary_transport transportsUnary
                                    (hsame_symm sameTransports), provenancePkg⟩
                            | inr rest =>
                                cases rest with
                                | inl sameRoutes =>
                                    exact
                                      ⟨unary_transport routesUnary
                                        (hsame_symm sameRoutes), provenancePkg⟩
                                | inr rest =>
                                    cases rest with
                                    | inl sameProvenance =>
                                        exact
                                          ⟨unary_transport provenanceUnary
                                            (hsame_symm sameProvenance), provenancePkg⟩
                                    | inr rest =>
                                        cases rest with
                                        | inl sameName =>
                                            exact
                                              ⟨unary_transport nameUnary
                                                (hsame_symm sameName), provenancePkg⟩
                                        | inr sameRoot =>
                                            exact
                                              ⟨unary_transport rootSourceUnary
                                                (hsame_symm sameRoot), provenancePkg⟩
    }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, rootSourceUnary,
      typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
      routesNameRootSource, namePkg, provenancePkg, rootSourcePkg⟩

end BEDC.Derived.ZnormalUp
