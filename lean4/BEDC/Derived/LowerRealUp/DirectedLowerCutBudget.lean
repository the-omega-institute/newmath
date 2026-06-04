import BEDC.Derived.LowerRealUp.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerRealDirectedLowerCutBudget [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerLeft lowerRight commonRead windowRead rationalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont L0 W lowerLeft ->
                Cont L0 W lowerRight ->
                  Cont lowerLeft lowerRight commonRead ->
                    Cont commonRead W windowRead ->
                      Cont windowRead R rationalRead ->
                        Cont rationalRead E realRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row L0 ∨ hsame row W ∨ hsame row R ∨
                                      hsame row E ∨ hsame row commonRead ∨ hsame row realRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont L0 W lowerLeft ∧
                                      Cont L0 W lowerRight ∧
                                        Cont lowerLeft lowerRight commonRead ∧
                                          Cont commonRead W windowRead ∧
                                            Cont windowRead R rationalRead ∧
                                              Cont rationalRead E realRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory commonRead ∧
                                  UnaryHistory windowRead ∧
                                    UnaryHistory rationalRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows l0Unary wUnary rUnary eUnary lowerLeftRoute lowerRightRoute commonRoute
    windowRoute rationalRoute realRoute provenancePkg namePkg
  cases fieldRows
  have lowerLeftUnary : UnaryHistory lowerLeft :=
    unary_cont_closed l0Unary wUnary lowerLeftRoute
  have lowerRightUnary : UnaryHistory lowerRight :=
    unary_cont_closed l0Unary wUnary lowerRightRoute
  have commonUnary : UnaryHistory commonRead :=
    unary_cont_closed lowerLeftUnary lowerRightUnary commonRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed commonUnary wUnary windowRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row commonRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L0 W lowerLeft ∧ Cont L0 W lowerRight ∧
              Cont lowerLeft lowerRight commonRead ∧ Cont commonRead W windowRead ∧
                Cont windowRead R rationalRead ∧ Cont rationalRead E realRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        ⟨source.right, lowerLeftRoute, lowerRightRoute, commonRoute, windowRoute,
          rationalRoute, realRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, commonUnary, windowUnary, rationalUnary, realUnary⟩

end BEDC.Derived.LowerRealUp
