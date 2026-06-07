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

theorem CalculusRootUnblockRealOperationLedger [AskSetup] [PackageSetup]
    {C D I L R Q Y _H _T P N derivativeRead integralRead limitRead dyadicRead realRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  UnaryHistory N →
                    Cont C D derivativeRead →
                      Cont C I integralRead →
                        Cont C L limitRead →
                          Cont Q Y dyadicRead →
                            Cont dyadicRead R realRead →
                              Cont realRead N publicRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle publicRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row publicRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row C ∨ hsame row D ∨ hsame row I ∨
                                            hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                              hsame row R ∨ hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont C D derivativeRead ∧
                                            Cont C I integralRead ∧ Cont C L limitRead ∧
                                              Cont Q Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                                                Cont realRead N publicRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle publicRead pkg)
                                        hsame ∧
                                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary iUnary lUnary qUnary yUnary _rUnary nUnary derivativeRoute
    integralRoute limitRoute dyadicRoute realRoute publicRoute provenancePkg publicPkg
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary yUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary _rUnary realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row Q ∨
              hsame row Y ∨ hsame row R ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont C L limitRead ∧ Cont Q Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                Cont realRead N publicRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, limitRoute, dyadicRoute, realRoute,
          publicRoute, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.CalculusUp
