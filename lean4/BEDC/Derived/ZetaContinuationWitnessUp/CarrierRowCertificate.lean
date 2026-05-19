import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_carrier_row_certificate
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name carrierRead →
            PkgSig bundle carrierRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
                      hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                        hsame row transports ∨ hsame row routes ∨ hsame row provenance ∨
                          hsame row name ∨ hsame row carrierRead)
                  (fun _row : BHist =>
                    Cont basic eta analytic ∧ Cont analytic functional transports ∧
                      Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                        Cont routes name carrierRead)
                  (fun row : BHist => hsame row row)
                  hsame ∧
                UnaryHistory carrierRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle carrierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet routesUnary nameUnary routesNameCarrier carrierPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have carrierUnary : UnaryHistory carrierRead :=
    unary_cont_closed routesUnary nameUnary routesNameCarrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row transports ∨ hsame row routes ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row carrierRead)
          (fun _row : BHist =>
            Cont basic eta analytic ∧ Cont analytic functional transports ∧
              Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                Cont routes name carrierRead)
          (fun row : BHist => hsame row row)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basic (Or.inl (hsame_refl basic))
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
        cases source with
        | inl sameBasic =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBasic)
        | inr rest =>
            cases rest with
            | inl sameEta =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEta))
            | inr rest =>
                cases rest with
                | inl sameAnalytic =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameAnalytic)))
                | inr rest =>
                    cases rest with
                    | inl samePole =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) samePole))))
                    | inr rest =>
                        cases rest with
                        | inl sameFunctional =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameFunctional)))))
                        | inr rest =>
                            cases rest with
                            | inl sameZeroLedger =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameZeroLedger))))))
                            | inr rest =>
                                cases rest with
                                | inl sameGamma =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameGamma)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameTransports =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameTransports))))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameRoutes =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameRoutes)))))))))
                                        | inr rest =>
                                            cases rest with
                                            | inl sameProvenance =>
                                                exact
                                                  Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inl
                                                                      (hsame_trans
                                                                        (hsame_symm sameRows)
                                                                        sameProvenance))))))))))
                                            | inr rest =>
                                                cases rest with
                                                | inl sameName =>
                                                    exact
                                                      Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      (Or.inr
                                                                        (Or.inr
                                                                          (Or.inl
                                                                            (hsame_trans
                                                                              (hsame_symm
                                                                                sameRows)
                                                                              sameName)))))))))))
                                                | inr sameCarrier =>
                                                    exact
                                                      Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      (Or.inr
                                                                        (Or.inr
                                                                          (Or.inr
                                                                            (hsame_trans
                                                                              (hsame_symm
                                                                                sameRows)
                                                                              sameCarrier)))))))))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
          transportsRoutesProvenance, routesNameCarrier⟩
    ledger_sound := by
      intro row _source
      exact hsame_refl row
  }
  exact ⟨cert, carrierUnary, namePkg, provenancePkg, carrierPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
