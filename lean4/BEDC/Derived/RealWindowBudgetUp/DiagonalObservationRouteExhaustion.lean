import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_diagonal_observation_route_exhaustion [AskSetup]
    [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont selector disclosure diagonalRead →
        PkgSig bundle diagonalRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                    disclosure transport route provenance nameRow bundle pkg ∧
                  (hsame row request ∨ hsame row windows ∨ hsame row dyadic ∨
                    hsame row handoff ∨ hsame row realSeal ∨ hsame row diagonalRead))
              (fun row : BHist =>
                Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                  Cont selector disclosure diagonalRead ∧
                    (hsame row request ∨ hsame row windows ∨ hsame row dyadic ∨
                      hsame row handoff ∨ hsame row realSeal ∨ hsame row diagonalRead))
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle diagonalRead pkg)
              hsame ∧
            UnaryHistory diagonalRead ∧ Cont request windows dyadic ∧
              Cont dyadic handoff realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier selectorDisclosureDiagonal diagonalPkg
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed carrier.selector_unary carrier.disclosure_unary
      selectorDisclosureDiagonal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                disclosure transport route provenance nameRow bundle pkg ∧
              (hsame row request ∨ hsame row windows ∨ hsame row dyadic ∨
                hsame row handoff ∨ hsame row realSeal ∨ hsame row diagonalRead))
          (fun row : BHist =>
            Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
              Cont selector disclosure diagonalRead ∧
                (hsame row request ∨ hsame row windows ∨ hsame row dyadic ∨
                  hsame row handoff ∨ hsame row realSeal ∨ hsame row diagonalRead))
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg)
          hsame := {
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
        intro _row _other same source
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
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic)))
                | inr tail =>
                    cases tail with
                    | inl rowHandoff =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm same) rowHandoff))))
                    | inr tail =>
                        cases tail with
                        | inl rowRealSeal =>
                            exact Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm same) rowRealSeal)))))
                        | inr rowDiagonal =>
                            exact Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr
                                (hsame_trans (hsame_symm same) rowDiagonal)))))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨carrier.request_windows_dyadic, carrier.dyadic_handoff_realSeal,
          selectorDisclosureDiagonal, source.right⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
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
                            exact unary_transport carrier.realSeal_unary
                              (hsame_symm rowRealSeal)
                        | inr rowDiagonal =>
                            exact unary_transport diagonalUnary (hsame_symm rowDiagonal)
      exact ⟨rowUnary, carrier.provenance_pkg, diagonalPkg⟩
  }
  exact
    ⟨cert, diagonalUnary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal⟩

end BEDC.Derived.RealWindowBudgetUp
