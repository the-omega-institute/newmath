import BEDC.Derived.CauchyCompletionAssociativityUp.FlatteningRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyCompletionAssociativityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionAssociativityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M U V I L S R D E F G H C P N leftIdem rightIdem leftCounit rightCounit
      leftMinimal rightMinimal leftStream rightStream leftDyadic rightDyadic leftRegular
      rightRegular leftReal rightReal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory G →
        UnaryHistory I →
          UnaryHistory V →
            UnaryHistory L →
              UnaryHistory S →
                UnaryHistory D →
                  UnaryHistory R →
                    UnaryHistory E →
                      hsame F G →
                        Cont F I leftIdem →
                          Cont G I rightIdem →
                            Cont leftIdem V leftCounit →
                              Cont rightIdem V rightCounit →
                                Cont leftCounit L leftMinimal →
                                  Cont rightCounit L rightMinimal →
                                    Cont leftMinimal S leftStream →
                                      Cont rightMinimal S rightStream →
                                        Cont leftStream D leftDyadic →
                                          Cont rightStream D rightDyadic →
                                            Cont leftDyadic R leftRegular →
                                              Cont rightDyadic R rightRegular →
                                                Cont leftRegular E leftReal →
                                                  Cont rightRegular E rightReal →
                                                    PkgSig bundle P pkg →
                                                      PkgSig bundle leftReal pkg →
                                                        PkgSig bundle rightReal pkg →
                                                          SemanticNameCert
                                                              (fun row : BHist =>
                                                                (hsame row leftReal ∨
                                                                    hsame row rightReal) ∧
                                                                  UnaryHistory row)
                                                              (fun row : BHist =>
                                                                hsame row F ∨ hsame row G ∨
                                                                  hsame row I ∨ hsame row V ∨
                                                                    hsame row L ∨
                                                                      hsame row S ∨
                                                                        hsame row D ∨
                                                                          hsame row R ∨
                                                                            hsame row E ∨
                                                                              hsame row leftReal ∨
                                                                                hsame row rightReal)
                                                              (fun row : BHist =>
                                                                (hsame row leftReal ∨
                                                                    hsame row rightReal) ∧
                                                                  PkgSig bundle P pkg)
                                                              hsame ∧ hsame leftReal rightReal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro leftUnary rightUnary idemUnary counitUnary minimalUnary streamUnary dyadicUnary
    regularUnary realUnary sameRoute leftIdemRoute rightIdemRoute leftCounitRoute
    rightCounitRoute leftMinimalRoute rightMinimalRoute leftStreamRoute rightStreamRoute
    leftDyadicRoute rightDyadicRoute leftRegularRoute rightRegularRoute leftRealRoute
    rightRealRoute provenancePkg _leftPkg _rightPkg
  have leftIdemUnary : UnaryHistory leftIdem :=
    unary_cont_closed leftUnary idemUnary leftIdemRoute
  have rightIdemUnary : UnaryHistory rightIdem :=
    unary_cont_closed rightUnary idemUnary rightIdemRoute
  have leftCounitUnary : UnaryHistory leftCounit :=
    unary_cont_closed leftIdemUnary counitUnary leftCounitRoute
  have rightCounitUnary : UnaryHistory rightCounit :=
    unary_cont_closed rightIdemUnary counitUnary rightCounitRoute
  have leftMinimalUnary : UnaryHistory leftMinimal :=
    unary_cont_closed leftCounitUnary minimalUnary leftMinimalRoute
  have rightMinimalUnary : UnaryHistory rightMinimal :=
    unary_cont_closed rightCounitUnary minimalUnary rightMinimalRoute
  have leftStreamUnary : UnaryHistory leftStream :=
    unary_cont_closed leftMinimalUnary streamUnary leftStreamRoute
  have rightStreamUnary : UnaryHistory rightStream :=
    unary_cont_closed rightMinimalUnary streamUnary rightStreamRoute
  have leftDyadicUnary : UnaryHistory leftDyadic :=
    unary_cont_closed leftStreamUnary dyadicUnary leftDyadicRoute
  have rightDyadicUnary : UnaryHistory rightDyadic :=
    unary_cont_closed rightStreamUnary dyadicUnary rightDyadicRoute
  have leftRegularUnary : UnaryHistory leftRegular :=
    unary_cont_closed leftDyadicUnary regularUnary leftRegularRoute
  have rightRegularUnary : UnaryHistory rightRegular :=
    unary_cont_closed rightDyadicUnary regularUnary rightRegularRoute
  have leftRealUnary : UnaryHistory leftReal :=
    unary_cont_closed leftRegularUnary realUnary leftRealRoute
  have rightRealUnary : UnaryHistory rightReal :=
    unary_cont_closed rightRegularUnary realUnary rightRealRoute
  have sameReal : hsame leftReal rightReal :=
    CauchyCompletionAssociativityFlatteningRoute leftUnary rightUnary idemUnary counitUnary
      minimalUnary streamUnary dyadicUnary regularUnary realUnary sameRoute leftIdemRoute
      rightIdemRoute leftCounitRoute rightCounitRoute leftMinimalRoute rightMinimalRoute
      leftStreamRoute rightStreamRoute leftDyadicRoute rightDyadicRoute leftRegularRoute
      rightRegularRoute leftRealRoute rightRealRoute provenancePkg _leftPkg _rightPkg
  have sourceRight : (hsame rightReal leftReal ∨ hsame rightReal rightReal) ∧
      UnaryHistory rightReal :=
    ⟨Or.inr (hsame_refl rightReal), rightRealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftReal ∨ hsame row rightReal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row G ∨ hsame row I ∨ hsame row V ∨ hsame row L ∨
              hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
                hsame row leftReal ∨ hsame row rightReal)
          (fun row : BHist =>
            (hsame row leftReal ∨ hsame row rightReal) ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro leftReal ⟨Or.inl (hsame_refl leftReal), leftRealUnary⟩
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
        intro row other sameRows sourceRow
        cases sourceRow.left with
        | inl sameLeft =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameLeft),
                unary_transport sourceRow.right sameRows⟩
        | inr sameRight =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameRight),
                unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left with
      | inl sameLeft =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl sameLeft)))))))))
      | inr sameRight =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr sameRight)))))))))
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.left, provenancePkg⟩
  }
  exact ⟨cert, sameReal⟩

end BEDC.Derived.CauchyCompletionAssociativityUp
