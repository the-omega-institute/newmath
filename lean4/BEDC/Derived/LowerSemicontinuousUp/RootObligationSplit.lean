import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootObligationSplit [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead valueRead epigraphRead packageRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont W R windowRead ->
                    Cont windowRead E valueRead ->
                      Cont valueRead O epigraphRead ->
                        Cont epigraphRead P packageRead ->
                          Cont packageRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row W ∨ hsame row R ∨ hsame row E ∨
                                        hsame row O ∨ hsame row P ∨ hsame row N ∨
                                          hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W R windowRead ∧
                                        Cont windowRead E valueRead ∧
                                          Cont valueRead O epigraphRead ∧
                                            Cont epigraphRead P packageRead ∧
                                              Cont packageRead N namedRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows wUnary rUnary eUnary oUnary pUnary nUnary windowRoute valueRoute
    epigraphRoute packageRoute namedRoute provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed windowUnary eUnary valueRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed valueUnary oUnary epigraphRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed epigraphUnary pUnary packageRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed packageUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row P ∨
              hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E valueRead ∧
              Cont valueRead O epigraphRead ∧ Cont epigraphRead P packageRead ∧
                Cont packageRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, windowRoute, valueRoute, epigraphRoute, packageRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
