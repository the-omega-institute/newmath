import BEDC.Derived.CauchyDifferenceCriterionUp.RegularTailStability

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionCarrier_bidirectional_exactness [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead zeroRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory Y ->
          UnaryHistory D ->
            UnaryHistory Z ->
              UnaryHistory Q ->
                UnaryHistory E ->
                  Cont X Y diffRead ->
                    Cont D Z nullRead ->
                      Cont nullRead Q zeroRead ->
                        Cont zeroRead E sealRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row diffRead ∨ hsame row sealRead) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                      hsame row Z ∨ hsame row Q ∨ hsame row E ∨
                                        Cont X Y diffRead ∨ Cont zeroRead E sealRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont X Y diffRead ∧
                                      Cont D Z nullRead ∧ Cont nullRead Q zeroRead ∧
                                        Cont zeroRead E sealRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory diffRead ∧ UnaryHistory nullRead ∧
                                  UnaryHistory zeroRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields xUnary yUnary dUnary zUnary qUnary eUnary diffRoute nullRoute zeroRoute
    sealRoute pPkg nPkg
  have _acceptedFields :
      cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := fields
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed xUnary yUnary diffRoute
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed dUnary zUnary nullRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed nullUnary qUnary zeroRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed zeroUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row diffRead ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row E ∨ Cont X Y diffRead ∨ Cont zeroRead E sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X Y diffRead ∧ Cont D Z nullRead ∧
              Cont nullRead Q zeroRead ∧ Cont zeroRead E sealRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨Or.inr (hsame_refl sealRead), sealUnary⟩
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
        constructor
        · cases source.left with
          | inl sameDiff =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDiff)
          | inr sameSeal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRoute))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, diffRoute, nullRoute, zeroRoute, sealRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, diffUnary, nullUnary, zeroUnary, sealUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
