import BEDC.Derived.StreamDiagonalSelectorUp

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamDiagonalSelectorPacket_scoped_status [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row schedule ∨ hsame row selector ∨ hsame row window ∨ hsame row readback ∨
            hsame row dyadicLedger ∨ hsame row diagonalPacket ∨ hsame row routes ∨
              hsame row provenance ∨ hsame row nameCert)
        (fun row : BHist =>
          hsame row schedule ∨ hsame row selector ∨ hsame row window ∨ hsame row readback ∨
            hsame row dyadicLedger ∨ hsame row diagonalPacket ∨ hsame row routes ∨
              hsame row provenance ∨ hsame row nameCert ∨ hsame row endpoint)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont schedule selector window ∧
            Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
              PkgSig bundle endpoint pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, routesUnary,
    provenanceUnary, nameCertUnary, windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro schedule (Or.inl (hsame_refl schedule))
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
        | inl rowSchedule =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowSchedule)
        | inr rest =>
            cases rest with
            | inl rowSelector =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowSelector))
            | inr rest =>
                cases rest with
                | inl rowWindow =>
                    exact
                      Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindow)))
                | inr rest =>
                    cases rest with
                    | inl rowReadback =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl
                                (hsame_trans (hsame_symm sameRows) rowReadback))))
                    | inr rest =>
                        cases rest with
                        | inl rowLedger =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl
                                      (hsame_trans (hsame_symm sameRows) rowLedger)))))
                        | inr rest =>
                            cases rest with
                            | inl rowDiagonal =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl
                                            (hsame_trans (hsame_symm sameRows)
                                              rowDiagonal))))))
                            | inr rest =>
                                cases rest with
                                | inl rowRoutes =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr (Or.inl
                                                  (hsame_trans (hsame_symm sameRows)
                                                    rowRoutes)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl rowProvenance =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr (Or.inl
                                                        (hsame_trans
                                                          (hsame_symm sameRows)
                                                          rowProvenance))))))))
                                    | inr rowNameCert =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            rowNameCert))))))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowSchedule =>
          exact Or.inl rowSchedule
      | inr rest =>
          cases rest with
          | inl rowSelector =>
              exact Or.inr (Or.inl rowSelector)
          | inr rest =>
              cases rest with
              | inl rowWindow =>
                  exact Or.inr (Or.inr (Or.inl rowWindow))
              | inr rest =>
                  cases rest with
                  | inl rowReadback =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl rowReadback)))
                  | inr rest =>
                      cases rest with
                      | inl rowLedger =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowLedger))))
                      | inr rest =>
                          cases rest with
                          | inl rowDiagonal =>
                              exact
                                Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowDiagonal)))))
                          | inr rest =>
                              cases rest with
                              | inl rowRoutes =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inr (Or.inr (Or.inl rowRoutes))))))
                              | inr rest =>
                                  cases rest with
                                  | inl rowProvenance =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr (Or.inl rowProvenance)))))))
                                  | inr rowNameCert =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr (Or.inl rowNameCert))))))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowSchedule =>
          exact
            ⟨unary_transport scheduleUnary (hsame_symm rowSchedule), windowRoute,
              ledgerRoute, endpointRoute, endpointPkg⟩
      | inr rest =>
          cases rest with
          | inl rowSelector =>
              exact
                ⟨unary_transport selectorUnary (hsame_symm rowSelector), windowRoute,
                  ledgerRoute, endpointRoute, endpointPkg⟩
          | inr rest =>
              cases rest with
              | inl rowWindow =>
                  exact
                    ⟨unary_transport windowUnary (hsame_symm rowWindow), windowRoute,
                      ledgerRoute, endpointRoute, endpointPkg⟩
              | inr rest =>
                  cases rest with
                  | inl rowReadback =>
                      exact
                        ⟨unary_transport readbackUnary (hsame_symm rowReadback), windowRoute,
                          ledgerRoute, endpointRoute, endpointPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl rowLedger =>
                          exact
                            ⟨unary_transport dyadicLedgerUnary (hsame_symm rowLedger),
                              windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩
                      | inr rest =>
                          cases rest with
                          | inl rowDiagonal =>
                              exact
                                ⟨unary_transport diagonalUnary (hsame_symm rowDiagonal),
                                  windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩
                          | inr rest =>
                              cases rest with
                              | inl rowRoutes =>
                                  exact
                                    ⟨unary_transport routesUnary (hsame_symm rowRoutes),
                                      windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩
                              | inr rest =>
                                  cases rest with
                                  | inl rowProvenance =>
                                      exact
                                        ⟨unary_transport provenanceUnary
                                            (hsame_symm rowProvenance),
                                          windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩
                                  | inr rowNameCert =>
                                      exact
                                        ⟨unary_transport nameCertUnary
                                            (hsame_symm rowNameCert),
                                          windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩
  }

end BEDC.Derived.StreamDiagonalSelectorUp
