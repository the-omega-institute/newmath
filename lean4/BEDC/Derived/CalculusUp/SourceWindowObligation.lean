import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusSourceWindowObligation [AskSetup] [PackageSetup]
    {R L C D I Q H T P N derivativeWindow integralWindow limitWindow realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory L ->
        UnaryHistory C ->
          UnaryHistory D ->
            UnaryHistory I ->
              UnaryHistory Q ->
                UnaryHistory H ->
                  UnaryHistory T ->
                    Cont D Q derivativeWindow ->
                      Cont I Q integralWindow ->
                        Cont L C limitWindow ->
                          Cont derivativeWindow R realRead ->
                            Cont realRead T namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row D ∨ hsame row I ∨ hsame row L ∨
                                          hsame row C ∨ hsame row Q ∨ hsame row R ∨
                                            hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont D Q derivativeWindow ∧
                                          Cont I Q integralWindow ∧ Cont L C limitWindow ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory derivativeWindow ∧
                                      UnaryHistory integralWindow ∧
                                        UnaryHistory limitWindow ∧ UnaryHistory realRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rUnary lUnary cUnary dUnary iUnary qUnary _hUnary tUnary derivativeRoute
    integralRoute limitRoute realRoute namedRoute provenancePkg namePkg
  have derivativeUnary : UnaryHistory derivativeWindow :=
    unary_cont_closed dUnary qUnary derivativeRoute
  have integralUnary : UnaryHistory integralWindow :=
    unary_cont_closed iUnary qUnary integralRoute
  have limitUnary : UnaryHistory limitWindow :=
    unary_cont_closed lUnary cUnary limitRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed derivativeUnary rUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary tUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, derivativeRoute, integralRoute, limitRoute, provenancePkg,
            namePkg⟩
    }
  · exact ⟨derivativeUnary, integralUnary, limitUnary, realUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
