import BEDC.Derived.CalculusUp.RootUnblockRiemannEndpointReadback

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootRiemannSumRealSeal [AskSetup] [PackageSetup]
    {C I R Q Y N P integralRead dyadicRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory I ->
        UnaryHistory Q ->
          UnaryHistory Y ->
            UnaryHistory R ->
              UnaryHistory N ->
                Cont C I integralRead ->
                  Cont Q Y dyadicRead ->
                    Cont dyadicRead R realRead ->
                      Cont realRead N namedRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle namedRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row I ∨ hsame row Q ∨ hsame row Y ∨
                                    hsame row R ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont C I integralRead ∧
                                    Cont Q Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                                      Cont realRead N namedRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle namedRead pkg)
                                hsame ∧
                              UnaryHistory integralRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary iUnary qUnary yUnary rUnary nUnary integralRoute dyadicRoute realRoute
    namedRoute provenancePkg namedPkg
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary yUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, integralRoute, dyadicRoute, realRoute, namedRoute,
            provenancePkg, namedPkg⟩
    }
  · exact ⟨integralUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
