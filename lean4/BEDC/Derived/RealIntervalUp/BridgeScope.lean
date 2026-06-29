import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalBridgeScope [AskSetup] [PackageSetup]
    {L U E D W R S H C P N endpointRead windowRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory P → UnaryHistory N → Cont L U endpointRead →
        Cont D W R → Cont R E S → Cont S H C → Cont C P windowRead →
          Cont windowRead N bridgeRead → PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row L ∨ hsame row U ∨ hsame row endpointRead ∨ hsame row D ∨
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row S ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row windowRead ∨
                        hsame row N ∨ hsame row bridgeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L U endpointRead ∧ Cont D W R ∧ Cont R E S ∧
                    Cont S H C ∧ Cont C P windowRead ∧ Cont windowRead N bridgeRead ∧
                      PkgSig bundle N pkg)
                hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory R ∧ UnaryHistory S ∧
              UnaryHistory C ∧ UnaryHistory windowRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro lUnary uUnary eUnary dUnary wUnary hUnary pUnary nUnary endpointRoute windowRoute
    sealRoute consumerRoute publicRoute bridgeRoute namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed consumerUnary pUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed windowUnary nUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row endpointRead ∨ hsame row D ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row S ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row windowRead ∨ hsame row N ∨
                  hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont D W R ∧ Cont R E S ∧
              Cont S H C ∧ Cont C P windowRead ∧ Cont windowRead N bridgeRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, endpointRoute, windowRoute, sealRoute, consumerRoute, publicRoute,
          bridgeRoute, namePkg⟩
  }
  exact
    ⟨cert, endpointUnary, readbackUnary, sealUnary, consumerUnary, windowUnary, bridgeUnary⟩

end BEDC.Derived.RealIntervalUp
