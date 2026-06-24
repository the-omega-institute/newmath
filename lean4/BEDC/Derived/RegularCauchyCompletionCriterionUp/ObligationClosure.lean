import BEDC.Derived.RegularCauchyCompletionCriterionUp.RealSealHandoff

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCompletionCriterionObligationClosure [AskSetup] [PackageSetup]
    {R W D M L Q H C P N windowRead toleranceRead modulusRead limitRead completionRead
      realRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionCriterionCarrier R W D M L Q H C P N bundle pkg →
      Cont W D windowRead →
        Cont windowRead R toleranceRead →
          Cont toleranceRead M modulusRead →
            Cont modulusRead L limitRead →
              Cont limitRead Q completionRead →
                Cont completionRead P realRead →
                  Cont Q N refusalRead →
                    PkgSig bundle realRead pkg →
                      PkgSig bundle refusalRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row realRead ∨ hsame row refusalRead) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row W ∨ hsame row D ∨
                                hsame row M ∨ hsame row L ∨ hsame row Q ∨
                                  hsame row H ∨ hsame row C ∨ hsame row P ∨
                                    hsame row N ∨ hsame row realRead ∨
                                      hsame row refusalRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle realRead pkg ∧
                                PkgSig bundle refusalRead pkg)
                            hsame ∧
                          UnaryHistory realRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier windowRoute toleranceRoute modulusRoute limitRoute completionRoute realRoute
    refusalRoute realPkg refusalPkg
  obtain ⟨rUnary, wUnary, dUnary, mUnary, lUnary, qUnary, _hUnary, _cUnary, pUnary,
    nUnary, _pkgP, _pkgN⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary rUnary toleranceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary qUnary completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed completionUnary pUnary realRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed qUnary nUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row realRead ∨ hsame row refusalRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨
              hsame row L ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row realRead ∨
                  hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realRead pkg ∧
              PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨Or.inl (hsame_refl realRead), realUnary⟩
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
        cases source.left with
        | inl sameReal =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameReal),
                unary_transport source.right sameRows⟩
        | inr sameRefusal =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameReal =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameReal
      | inr sameRefusal =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr sameRefusal
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realPkg, refusalPkg⟩
  }
  exact ⟨cert, realUnary, refusalUnary⟩

end BEDC.Derived.RegularCauchyCompletionCriterionUp
