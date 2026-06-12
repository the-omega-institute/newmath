import BEDC.Derived.CalculusUp.RootPublicPackageReadiness

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootPackageNonescape [AskSetup] [PackageSetup]
    {R L C D I Q H T P N derivativeRead integralRead limitRead realRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory L ->
        UnaryHistory C ->
          UnaryHistory D ->
            UnaryHistory I ->
              UnaryHistory Q ->
                UnaryHistory T ->
                  UnaryHistory N ->
                    Cont C D derivativeRead ->
                      Cont C I integralRead ->
                        Cont C L limitRead ->
                          Cont Q R realRead ->
                            Cont realRead T publicRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row publicRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row C ∨ hsame row D ∨ hsame row I ∨
                                          hsame row L ∨ hsame row Q ∨ hsame row R ∨
                                            hsame row publicRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont C D derivativeRead ∧
                                          Cont C I integralRead ∧ Cont C L limitRead ∧
                                            Cont Q R realRead ∧
                                              Cont realRead T publicRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                      hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rUnary lUnary cUnary dUnary iUnary qUnary tUnary _nUnary derivativeRoute
    integralRoute limitRoute realRoute publicRoute provenancePkg namePkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed qUnary rUnary realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary tUnary publicRoute
  constructor
  · exact {
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, derivativeRoute, integralRoute, limitRoute, realRoute,
            publicRoute, provenancePkg, namePkg⟩
    }
  · exact publicUnary

end BEDC.Derived.CalculusUp
