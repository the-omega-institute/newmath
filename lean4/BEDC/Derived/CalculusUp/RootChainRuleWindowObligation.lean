import BEDC.Derived.CalculusUp.RootPublicPackageReadiness

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootChainRuleWindowObligation [AskSetup] [PackageSetup]
    {C D L Q Y R H T P N outerGraph innerGraph derivativeOuter derivativeInner limitRead
      rationalRead dyadicRead realRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory D ->
        UnaryHistory L ->
          UnaryHistory Q ->
            UnaryHistory Y ->
              UnaryHistory R ->
                UnaryHistory T ->
                  Cont C C outerGraph ->
                    Cont outerGraph C innerGraph ->
                      Cont innerGraph D derivativeOuter ->
                        Cont derivativeOuter D derivativeInner ->
                          Cont derivativeInner L limitRead ->
                            Cont limitRead Q rationalRead ->
                              Cont rationalRead Y dyadicRead ->
                                Cont dyadicRead R realRead ->
                                  Cont realRead T replayRead ->
                                    hsame H (append P N) ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row replayRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row C ∨ hsame row D ∨ hsame row L ∨
                                                  hsame row Q ∨ hsame row Y ∨
                                                    hsame row R ∨ hsame row replayRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont C C outerGraph ∧
                                                  Cont outerGraph C innerGraph ∧
                                                    Cont innerGraph D derivativeOuter ∧
                                                      Cont derivativeOuter D derivativeInner ∧
                                                        Cont derivativeInner L limitRead ∧
                                                          Cont limitRead Q rationalRead ∧
                                                            Cont rationalRead Y dyadicRead ∧
                                                              Cont dyadicRead R realRead ∧
                                                                Cont realRead T replayRead ∧
                                                                  hsame H (append P N) ∧
                                                                    PkgSig bundle P pkg ∧
                                                                      PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory outerGraph ∧ UnaryHistory innerGraph ∧
                                              UnaryHistory derivativeOuter ∧
                                                UnaryHistory derivativeInner ∧
                                                  UnaryHistory limitRead ∧
                                                    UnaryHistory rationalRead ∧
                                                      UnaryHistory dyadicRead ∧
                                                        UnaryHistory realRead ∧
                                                          UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryC unaryD unaryL unaryQ unaryY unaryR unaryT outerRoute innerRoute
    derivativeOuterRoute derivativeInnerRoute limitRoute rationalRoute dyadicRoute realRoute
    replayRoute transportSame provenancePkg namePkg
  have outerUnary : UnaryHistory outerGraph :=
    unary_cont_closed unaryC unaryC outerRoute
  have innerUnary : UnaryHistory innerGraph :=
    unary_cont_closed outerUnary unaryC innerRoute
  have derivativeOuterUnary : UnaryHistory derivativeOuter :=
    unary_cont_closed innerUnary unaryD derivativeOuterRoute
  have derivativeInnerUnary : UnaryHistory derivativeInner :=
    unary_cont_closed derivativeOuterUnary unaryD derivativeInnerRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed derivativeInnerUnary unaryL limitRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed limitUnary unaryQ rationalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed rationalUnary unaryY dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary unaryR realRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed realUnary unaryT replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row L ∨ hsame row Q ∨ hsame row Y ∨
              hsame row R ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C C outerGraph ∧ Cont outerGraph C innerGraph ∧
              Cont innerGraph D derivativeOuter ∧ Cont derivativeOuter D derivativeInner ∧
                Cont derivativeInner L limitRead ∧ Cont limitRead Q rationalRead ∧
                  Cont rationalRead Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                    Cont realRead T replayRead ∧ hsame H (append P N) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, outerRoute, innerRoute, derivativeOuterRoute, derivativeInnerRoute,
          limitRoute, rationalRoute, dyadicRoute, realRoute, replayRoute, transportSame,
          provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, outerUnary, innerUnary, derivativeOuterUnary, derivativeInnerUnary, limitUnary,
      rationalUnary, dyadicUnary, realUnary, replayUnary⟩

end BEDC.Derived.CalculusUp
