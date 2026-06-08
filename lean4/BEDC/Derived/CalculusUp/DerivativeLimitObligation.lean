import BEDC.Derived.CalculusUp.RootOperationReadbackTailChainRuleBoundary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusDerivativeLimitObligation [AskSetup] [PackageSetup]
    {R L C D Q H T P N graphRead derivativeRead limitRead rationalRead realRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory L →
        UnaryHistory C →
          UnaryHistory D →
            UnaryHistory Q →
              UnaryHistory T →
                Cont C D graphRead →
                  Cont graphRead D derivativeRead →
                    Cont derivativeRead L limitRead →
                      Cont limitRead Q rationalRead →
                        Cont rationalRead R realRead →
                          Cont realRead T replayRead →
                            hsame H (append P N) →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row replayRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row R ∨ hsame row L ∨ hsame row C ∨
                                          hsame row D ∨ hsame row Q ∨ hsame row replayRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont C D graphRead ∧
                                          Cont graphRead D derivativeRead ∧
                                            Cont derivativeRead L limitRead ∧
                                              Cont limitRead Q rationalRead ∧
                                                Cont rationalRead R realRead ∧
                                                  Cont realRead T replayRead ∧
                                                    hsame H (append P N) ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory graphRead ∧ UnaryHistory derivativeRead ∧
                                      UnaryHistory limitRead ∧ UnaryHistory rationalRead ∧
                                        UnaryHistory realRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryR unaryL unaryC unaryD unaryQ unaryT graphRoute derivativeRoute limitRoute
    rationalRoute realRoute replayRoute transportSame provenancePkg namePkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed unaryC unaryD graphRoute
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed graphUnary unaryD derivativeRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed derivativeUnary unaryL limitRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed limitUnary unaryQ rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary unaryR realRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed realUnary unaryT replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row L ∨ hsame row C ∨ hsame row D ∨ hsame row Q ∨
              hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D graphRead ∧ Cont graphRead D derivativeRead ∧
              Cont derivativeRead L limitRead ∧ Cont limitRead Q rationalRead ∧
                Cont rationalRead R realRead ∧ Cont realRead T replayRead ∧
                  hsame H (append P N) ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, derivativeRoute, limitRoute, rationalRoute, realRoute,
          replayRoute, transportSame, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, graphUnary, derivativeUnary, limitUnary, rationalUnary, realUnary, replayUnary⟩

end BEDC.Derived.CalculusUp
