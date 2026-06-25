import BEDC.Derived.RealPolynomialUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealPolynomialUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPolynomialEvaluationStability [AskSetup] [PackageSetup]
    {A X Q S G W D E M H C P N coeffInput readback algebraWindow toleranceLedger
      evalRoute handoff named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory X ->
        UnaryHistory Q ->
          UnaryHistory S ->
            UnaryHistory G ->
              UnaryHistory W ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    UnaryHistory M ->
                      UnaryHistory H ->
                        Cont A X coeffInput ->
                          Cont Q S readback ->
                            Cont G W algebraWindow ->
                              Cont D E toleranceLedger ->
                                Cont coeffInput readback evalRoute ->
                                  Cont evalRoute algebraWindow handoff ->
                                    Cont H handoff named ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle named pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row named ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row A ∨ hsame row X ∨
                                                  hsame row Q ∨ hsame row S ∨
                                                    hsame row G ∨ hsame row W ∨
                                                      hsame row D ∨ hsame row E ∨
                                                        hsame row M ∨ hsame row H ∨
                                                          hsame row C ∨ hsame row P ∨
                                                            hsame row N ∨
                                                              hsame row evalRoute ∨
                                                                hsame row named)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  Cont A X coeffInput ∧
                                                    Cont Q S readback ∧
                                                      Cont G W algebraWindow ∧
                                                        Cont D E toleranceLedger ∧
                                                          Cont coeffInput readback
                                                            evalRoute ∧
                                                            Cont evalRoute algebraWindow
                                                              handoff ∧
                                                              Cont H handoff named ∧
                                                                PkgSig bundle named pkg)
                                              hsame ∧
                                            UnaryHistory coeffInput ∧
                                              UnaryHistory readback ∧
                                                UnaryHistory algebraWindow ∧
                                                  UnaryHistory toleranceLedger ∧
                                                    UnaryHistory evalRoute ∧
                                                      UnaryHistory handoff ∧
                                                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro aUnary xUnary qUnary sUnary gUnary wUnary dUnary eUnary _mUnary hUnary
    coeffRoute readbackRoute algebraRoute toleranceRoute evalRouteStep handoffRoute
    namedRoute _packageRead namedPkg
  have coeffUnary : UnaryHistory coeffInput :=
    unary_cont_closed aUnary xUnary coeffRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed qUnary sUnary readbackRoute
  have algebraUnary : UnaryHistory algebraWindow :=
    unary_cont_closed gUnary wUnary algebraRoute
  have toleranceUnary : UnaryHistory toleranceLedger :=
    unary_cont_closed dUnary eUnary toleranceRoute
  have evalUnary : UnaryHistory evalRoute :=
    unary_cont_closed coeffUnary readbackUnary evalRouteStep
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed evalUnary algebraUnary handoffRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary handoffUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row X ∨ hsame row Q ∨ hsame row S ∨ hsame row G ∨
              hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row M ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row evalRoute ∨
                  hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A X coeffInput ∧ Cont Q S readback ∧
              Cont G W algebraWindow ∧ Cont D E toleranceLedger ∧
                Cont coeffInput readback evalRoute ∧ Cont evalRoute algebraWindow handoff ∧
                  Cont H handoff named ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        ⟨source.right, coeffRoute, readbackRoute, algebraRoute, toleranceRoute,
          evalRouteStep, handoffRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, coeffUnary, readbackUnary, algebraUnary, toleranceUnary, evalUnary,
      handoffUnary, namedUnary⟩

end BEDC.Derived.RealPolynomialUp
