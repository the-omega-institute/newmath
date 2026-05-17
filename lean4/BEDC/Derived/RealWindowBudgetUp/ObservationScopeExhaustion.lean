import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp.ObservationScopeExhaustion

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_observation_scope_exhaustion [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont realSeal selector scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                disclosure transport route provenance nameRow bundle pkg ∧
                (hsame row request ∨ hsame row windows ∨ hsame row dyadic ∨
                  hsame row handoff ∨ hsame row realSeal ∨ hsame row selector ∨
                    hsame row disclosure ∨ hsame row transport ∨ hsame row route ∨
                      hsame row provenance ∨ hsame row nameRow ∨ hsame row scopedRead))
            (fun row : BHist => UnaryHistory row)
            (fun _row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
                PkgSig bundle scopedRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier scopedRoute scopedPkg
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed carrier.realSeal_unary carrier.selector_unary scopedRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro request ⟨carrier, Or.inl (hsame_refl request)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowRequest =>
            exact Or.inl (hsame_trans (hsame_symm same) rowRequest)
        | inr tail =>
            cases tail with
            | inl rowWindows =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowWindows))
            | inr tail =>
                cases tail with
                | inl rowDyadic =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic)))
                | inr tail =>
                    cases tail with
                    | inl rowHandoff =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowHandoff))))
                    | inr tail =>
                        cases tail with
                        | inl rowRealSeal =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm same) rowRealSeal)))))
                        | inr tail =>
                            cases tail with
                            | inl rowSelector =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm same)
                                              rowSelector))))))
                            | inr tail =>
                                cases tail with
                                | inl rowDisclosure =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inl
                                                  (hsame_trans (hsame_symm same)
                                                    rowDisclosure)))))))
                                | inr tail =>
                                    cases tail with
                                    | inl rowTransport =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inl
                                                        (hsame_trans (hsame_symm same)
                                                          rowTransport))))))))
                                    | inr tail =>
                                        cases tail with
                                        | inl rowRoute =>
                                            exact Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inl
                                                              (hsame_trans
                                                                (hsame_symm same)
                                                                rowRoute)))))))))
                                        | inr tail =>
                                            cases tail with
                                            | inl rowProvenance =>
                                                exact Or.inr
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
                                                                      (hsame_symm same)
                                                                      rowProvenance))))))))))
                                            | inr tail =>
                                                cases tail with
                                                | inl rowName =>
                                                    exact Or.inr
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
                                                                            (hsame_symm same)
                                                                            rowName)))))))))))
                                                | inr rowScoped =>
                                                    exact Or.inr
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
                                                                            (hsame_symm same)
                                                                            rowScoped)))))))))))
    }
    pattern_sound := by
      intro row source
      cases source.right with
      | inl rowRequest =>
          exact unary_transport carrier.request_unary (hsame_symm rowRequest)
      | inr tail =>
          cases tail with
          | inl rowWindows =>
              exact unary_transport carrier.windows_unary (hsame_symm rowWindows)
          | inr tail =>
              cases tail with
              | inl rowDyadic =>
                  exact unary_transport carrier.dyadic_unary (hsame_symm rowDyadic)
              | inr tail =>
                  cases tail with
                  | inl rowHandoff =>
                      exact unary_transport carrier.handoff_unary (hsame_symm rowHandoff)
                  | inr tail =>
                      cases tail with
                      | inl rowRealSeal =>
                          exact unary_transport carrier.realSeal_unary (hsame_symm rowRealSeal)
                      | inr tail =>
                          cases tail with
                          | inl rowSelector =>
                              exact unary_transport carrier.selector_unary (hsame_symm rowSelector)
                          | inr tail =>
                              cases tail with
                              | inl rowDisclosure =>
                                  exact unary_transport carrier.disclosure_unary
                                    (hsame_symm rowDisclosure)
                              | inr tail =>
                                  cases tail with
                                  | inl rowTransport =>
                                      exact unary_transport carrier.transport_unary
                                        (hsame_symm rowTransport)
                                  | inr tail =>
                                      cases tail with
                                      | inl rowRoute =>
                                          exact unary_transport carrier.route_unary
                                            (hsame_symm rowRoute)
                                      | inr tail =>
                                          cases tail with
                                          | inl rowProvenance =>
                                              exact unary_transport carrier.provenance_unary
                                                (hsame_symm rowProvenance)
                                          | inr tail =>
                                              cases tail with
                                              | inl rowName =>
                                                  exact unary_transport carrier.nameRow_unary
                                                    (hsame_symm rowName)
                                              | inr rowScoped =>
                                                  exact unary_transport scopedUnary
                                                    (hsame_symm rowScoped)
    ledger_sound := by
      intro _row _source
      exact ⟨carrier.provenance_pkg, carrier.nameRow_pkg, scopedPkg⟩
  }

end BEDC.Derived.RealWindowBudgetUp.ObservationScopeExhaustion
