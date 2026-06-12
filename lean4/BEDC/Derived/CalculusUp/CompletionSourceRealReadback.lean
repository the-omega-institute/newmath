import BEDC.Derived.CalculusUp.CompletionSourceEnvelopeObligations

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusCompletionSourceRealReadback [AskSetup] [PackageSetup]
    {R L C D I Q Y N P derivativeRead integralRead limitRead dyadicRead realRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory L ->
        UnaryHistory C ->
          UnaryHistory D ->
            UnaryHistory I ->
              UnaryHistory Q ->
                UnaryHistory Y ->
                  UnaryHistory N ->
                    Cont C D derivativeRead ->
                      Cont C I integralRead ->
                        Cont C L limitRead ->
                          Cont Q Y dyadicRead ->
                            Cont dyadicRead R realRead ->
                              Cont realRead N publicRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle publicRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row realRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row Q ∨ hsame row Y ∨ hsame row R ∨
                                            hsame row realRead ∨ hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont Q Y dyadicRead ∧
                                            Cont dyadicRead R realRead ∧
                                              Cont realRead N publicRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle publicRead pkg)
                                        hsame ∧
                                      UnaryHistory dyadicRead ∧
                                        UnaryHistory realRead ∧
                                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro rUnary _lUnary _cUnary _dUnary _iUnary qUnary yUnary nUnary _derivativeRoute
    _integralRoute _limitRoute dyadicRoute realRoute publicRoute provenancePkg publicPkg
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary yUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nUnary publicRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, dyadicRoute, realRoute, publicRoute, provenancePkg, publicPkg⟩
    }
  · exact ⟨dyadicUnary, realUnary, publicUnary⟩

end BEDC.Derived.CalculusUp
