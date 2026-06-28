import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalEndpointOrderObligation [AskSetup] [PackageSetup]
    {L U E D W R S H C P N _orderRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory E ->
          UnaryHistory D ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory H ->
                  Cont L U E ->
                    Cont E R sealRead ->
                      Cont sealRead H replayRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row E ∨ hsame row sealRead ∨
                                      hsame row replayRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row L ∨ hsame row U ∨ hsame row E ∨
                                    hsame row D ∨ hsame row W ∨ hsame row R ∨
                                      hsame row sealRead ∨ hsame row S ∨ hsame row H ∨
                                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                                          hsame row replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont L U E ∧ Cont E R sealRead ∧
                                    Cont sealRead H replayRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory E ∧ UnaryHistory sealRead ∧
                                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro _lUnary _uUnary eUnary _dUnary _wUnary rUnary hUnary orderRoute sealRoute
    replayRoute provenancePkg namePkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed eUnary rUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary hUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row E ∨ hsame row sealRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row sealRead ∨ hsame row S ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U E ∧ Cont E R sealRead ∧
              Cont sealRead H replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨Or.inl (hsame_refl E), eUnary⟩
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
        constructor
        · cases source.left with
          | inl sameEndpointOrder =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpointOrder)
          | inr tail =>
              cases tail with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEndpointOrder =>
          exact Or.inr (Or.inr (Or.inl sameEndpointOrder))
      | inr tail =>
          cases tail with
          | inl sameSeal =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSeal))))))
          | inr sameReplay =>
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
                                      (Or.inr sameReplay)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, orderRoute, sealRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, eUnary, sealUnary, replayUnary⟩

end BEDC.Derived.RealIntervalUp
