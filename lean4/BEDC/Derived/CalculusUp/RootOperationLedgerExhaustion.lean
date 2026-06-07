import BEDC.Derived.CalculusUp.TasteGate
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

theorem CalculusRootOperationLedgerExhaustion [AskSetup] [PackageSetup]
    {C D I L R Q Y H T P N derivativeRead integralRead limitRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  Cont C D derivativeRead →
                    Cont C I integralRead →
                      Cont C L limitRead →
                        Cont Q Y realRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row C ∨ hsame row D ∨ hsame row I ∨
                                      hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                        hsame row R ∨ hsame row realRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont C D derivativeRead ∧
                                      Cont C I integralRead ∧ Cont C L limitRead ∧
                                        Cont Q Y realRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                                  UnaryHistory limitRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary dUnary iUnary lUnary qUnary yUnary _rUnary derivativeRoute integralRoute
    limitRoute realRoute provenancePkg namePkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed qUnary yUnary realRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, derivativeRoute, integralRoute, limitRoute, realRoute,
            provenancePkg, namePkg⟩
    }
  · exact ⟨derivativeUnary, integralUnary, limitUnary, realUnary⟩

end BEDC.Derived.CalculusUp
