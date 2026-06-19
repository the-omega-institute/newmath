import BEDC.Derived.CalculusUp.RootRealSealNonescape

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusFiniteLimitSealPublicHandoff [AskSetup] [PackageSetup]
    {C D I L Q Y R H T P N derivativeRead integralRead endpointRead limitRead
      toleranceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory D ->
        UnaryHistory I ->
          UnaryHistory L ->
            UnaryHistory Q ->
              UnaryHistory Y ->
                UnaryHistory R ->
                  UnaryHistory N ->
                    Cont C D derivativeRead ->
                      Cont C I integralRead ->
                        Cont derivativeRead integralRead endpointRead ->
                          Cont C L limitRead ->
                            Cont Q Y toleranceRead ->
                              Cont toleranceRead R publicRead ->
                                Cont endpointRead publicRead N ->
                                  hsame H (append T P) ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row publicRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row C ∨ hsame row D ∨ hsame row I ∨
                                                hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                                  hsame row R ∨ hsame row endpointRead ∨
                                                    hsame row publicRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont C D derivativeRead ∧
                                                Cont C I integralRead ∧
                                                  Cont derivativeRead integralRead endpointRead ∧
                                                    Cont C L limitRead ∧
                                                      Cont Q Y toleranceRead ∧
                                                        Cont toleranceRead R publicRead ∧
                                                          hsame H (append T P))
                                            hsame ∧
                                          UnaryHistory derivativeRead ∧
                                            UnaryHistory integralRead ∧
                                              UnaryHistory endpointRead ∧
                                                UnaryHistory limitRead ∧
                                                  UnaryHistory toleranceRead ∧
                                                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary iUnary lUnary qUnary yUnary rUnary nUnary derivativeRoute
    integralRoute endpointRoute limitRoute toleranceRoute publicRoute nameRoute
    handoffSame _provenancePkg _namePkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeUnary integralUnary endpointRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed qUnary yUnary toleranceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed toleranceUnary rUnary publicRoute
  have _nameUnary : UnaryHistory N :=
    unary_cont_closed endpointUnary publicUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨
              hsame row Q ∨ hsame row Y ∨ hsame row R ∨ hsame row endpointRead ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont derivativeRead integralRead endpointRead ∧ Cont C L limitRead ∧
                Cont Q Y toleranceRead ∧ Cont toleranceRead R publicRead ∧
                  hsame H (append T P))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, endpointRoute, limitRoute,
          toleranceRoute, publicRoute, handoffSame⟩
  }
  exact
    ⟨cert, derivativeUnary, integralUnary, endpointUnary, limitUnary, toleranceUnary,
      publicUnary⟩

end BEDC.Derived.CalculusUp
