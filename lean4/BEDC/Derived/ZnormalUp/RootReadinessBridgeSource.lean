import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_readiness_bridge_source [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name sourceRead
      sourceExport siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel sourceRead ->
        Cont sourceRead name sourceExport ->
          Cont normal continuation siblingRead ->
            PkgSig bundle sourceExport pkg ->
              PkgSig bundle siblingRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceExport ∨ hsame row siblingRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                      hsame row sourceExport ∨ hsame row normal ∨ hsame row continuation ∨
                        hsame row siblingRead)
                  (fun row : BHist =>
                    (hsame row sourceExport ∨ hsame row siblingRead) ∧
                      (PkgSig bundle sourceExport pkg ∨ PkgSig bundle siblingRead pkg))
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelSourceRead sourceReadNameSourceExport normalContinuationSiblingRead
    sourceExportPkg siblingReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelSourceRead
  have sourceExportUnary : UnaryHistory sourceExport :=
    unary_cont_closed sourceReadUnary nameUnary sourceReadNameSourceExport
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have sourceExportSource :
      (fun row : BHist =>
        (hsame row sourceExport ∨ hsame row siblingRead) ∧ UnaryHistory row)
        sourceExport := by
    exact ⟨Or.inl (hsame_refl sourceExport), sourceExportUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro sourceExport sourceExportSource
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
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr sameSibling =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSibling)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameSource)))
      | inr sameSibling =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sameSibling)))))
    ledger_sound := by
      intro _row source
      constructor
      · exact source.left
      · cases source.left with
        | inl _sameSource =>
            exact Or.inl sourceExportPkg
        | inr _sameSibling =>
            exact Or.inr siblingReadPkg
  }

theorem ZnormalPacket_source_route_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
              bundle pkg ∧
            (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row name))
        (fun row : BHist =>
          UnaryHistory row ∧ Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
            Cont continuation transports routes)
        (fun _row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert Cont hsame UnaryHistory
  intro packet
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro typed ⟨packetWitness, Or.inl (hsame_refl typed)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
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
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFuel))
              | inr rest =>
                  cases rest with
                  | inl sameTerminal =>
                      exact Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal)))
                  | inr rest =>
                      cases rest with
                      | inl sameNormal =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameNormal))))
                      | inr rest =>
                          cases rest with
                          | inl sameContinuation =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameContinuation)))))
                          | inr rest =>
                              cases rest with
                              | inl sameTransports =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
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
                                                (Or.inr
                                                  (Or.inl
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
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameProvenance))))))))
                                      | inr sameName =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameName))))))))
    }
    pattern_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl sameTyped =>
            exact unary_transport typedUnary (hsame_symm sameTyped)
        | inr rest =>
            cases rest with
            | inl sameFuel =>
                exact unary_transport fuelUnary (hsame_symm sameFuel)
            | inr rest =>
                cases rest with
                | inl sameTerminal =>
                    exact unary_transport terminalUnary (hsame_symm sameTerminal)
                | inr rest =>
                    cases rest with
                    | inl sameNormal =>
                        exact unary_transport normalUnary (hsame_symm sameNormal)
                    | inr rest =>
                        cases rest with
                        | inl sameContinuation =>
                            exact unary_transport continuationUnary
                              (hsame_symm sameContinuation)
                        | inr rest =>
                            cases rest with
                            | inl sameTransports =>
                                exact unary_transport transportsUnary
                                  (hsame_symm sameTransports)
                            | inr rest =>
                                cases rest with
                                | inl sameRoutes =>
                                    exact unary_transport routesUnary (hsame_symm sameRoutes)
                                | inr rest =>
                                    cases rest with
                                    | inl sameProvenance =>
                                        exact unary_transport provenanceUnary
                                          (hsame_symm sameProvenance)
                                    | inr sameName =>
                                        exact unary_transport nameUnary (hsame_symm sameName)
      exact
        ⟨rowUnary, typedFuelTerminal, terminalNormalContinuation,
          continuationTransportsRoutes⟩
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, namePkg⟩
  }

end BEDC.Derived.ZnormalUp
