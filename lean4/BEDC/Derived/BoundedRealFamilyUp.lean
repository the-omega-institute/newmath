import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedRealFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealFamilyLocatedUpperRow [AskSetup] [PackageSetup]
    {I W Q R B H C P N indexWindow streamRead rationalRead realRead boundRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory B ->
              UnaryHistory H ->
                UnaryHistory C ->
                  Cont I W indexWindow ->
                    Cont indexWindow Q streamRead ->
                      Cont streamRead R rationalRead ->
                        Cont rationalRead B realRead ->
                          Cont realRead H boundRead ->
                            Cont boundRead C replayRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row I ∨ hsame row W ∨ hsame row Q ∨
                                          hsame row R ∨ hsame row B ∨ hsame row boundRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont rationalRead B realRead ∧
                                          Cont realRead H boundRead ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory boundRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro iUnary wUnary qUnary rUnary bUnary hUnary cUnary indexRoute streamRoute
    rationalRoute realRoute boundRoute replayRoute provenancePkg localNamePkg
  have indexWindowUnary : UnaryHistory indexWindow :=
    unary_cont_closed iUnary wUnary indexRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed indexWindowUnary qUnary streamRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed streamReadUnary rUnary rationalRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary bUnary realRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed realReadUnary hUnary boundRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundReadUnary cUnary replayRoute
  have sourceBound :
      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row) boundRead := by
    exact ⟨hsame_refl boundRead, boundReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨ hsame row B ∨
              hsame row boundRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont rationalRead B realRead ∧ Cont realRead H boundRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundRead sourceBound
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
      exact ⟨source.right, realRoute, boundRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundReadUnary, replayReadUnary⟩

theorem BoundedRealFamilyRegSeqRatScope [AskSetup] [PackageSetup]
    {I W Q R B _H _C P N windowRead rationalRead realRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory B ->
              Cont I W windowRead ->
                Cont windowRead Q rationalRead ->
                  Cont rationalRead R realRead ->
                    Cont realRead B boundRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row W ∨ hsame row Q ∨ hsame row R ∨ hsame row B ∨
                                  hsame row realRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont windowRead Q rationalRead ∧
                                  Cont rationalRead R realRead ∧ Cont realRead B boundRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory rationalRead ∧ UnaryHistory realRead ∧
                              UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro iUnary wUnary qUnary rUnary bUnary windowRoute rationalRoute realRoute boundRoute
    provenancePkg localNamePkg
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed iUnary wUnary windowRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowReadUnary qUnary rationalRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary rUnary realRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed realReadUnary bUnary boundRoute
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row R ∨ hsame row B ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windowRead Q rationalRead ∧ Cont rationalRead R realRead ∧
              Cont realRead B boundRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
        ⟨source.right, rationalRoute, realRoute, boundRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, rationalReadUnary, realReadUnary, boundReadUnary⟩

end BEDC.Derived.BoundedRealFamilyUp
