import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalFormalTargetHandoff [AskSetup] [PackageSetup]
    {L U E D W R S H C P N endpointRead windowRead bridgeRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory P → UnaryHistory N → Cont L U endpointRead →
        Cont D W R → Cont R E S → Cont S H C → Cont C P windowRead →
          Cont windowRead N bridgeRead → Cont bridgeRead P targetRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                      hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row endpointRead ∨ hsame row windowRead ∨
                            hsame row bridgeRead ∨ hsame row targetRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L U endpointRead ∧ Cont D W R ∧
                      Cont R E S ∧ Cont S H C ∧ Cont C P windowRead ∧
                        Cont windowRead N bridgeRead ∧ Cont bridgeRead P targetRead ∧
                          PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory endpointRead ∧ UnaryHistory R ∧ UnaryHistory S ∧
                  UnaryHistory C ∧ UnaryHistory windowRead ∧ UnaryHistory bridgeRead ∧
                    UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro lUnary uUnary eUnary dUnary wUnary hUnary pUnary nUnary endpointRoute windowRoute
    sealRoute replayRoute publicRoute bridgeRoute targetRoute namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have replayUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary replayRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed replayUnary pUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed windowUnary nUnary bridgeRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed bridgeUnary pUnary targetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row endpointRead ∨ hsame row windowRead ∨
                  hsame row bridgeRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont D W R ∧ Cont R E S ∧
              Cont S H C ∧ Cont C P windowRead ∧ Cont windowRead N bridgeRead ∧
                Cont bridgeRead P targetRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead ⟨hsame_refl targetRead, targetUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
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
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, sealRoute, replayRoute, publicRoute,
          bridgeRoute, targetRoute, namePkg⟩
  }
  exact
    ⟨cert, endpointUnary, readbackUnary, sealUnary, replayUnary, windowUnary, bridgeUnary,
      targetUnary⟩

end BEDC.Derived.RealIntervalUp
