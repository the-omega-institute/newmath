import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphFilterRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead filterRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory C ->
                UnaryHistory N ->
                  Cont W R windowRead ->
                    Cont windowRead E epigraphRead ->
                      Cont epigraphRead O locatedRead ->
                        Cont locatedRead C filterRead ->
                          Cont filterRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row W ∨ hsame row R ∨ hsame row E ∨
                                        hsame row O ∨ hsame row C ∨ hsame row N ∨
                                          hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W R windowRead ∧
                                        Cont windowRead E epigraphRead ∧
                                          Cont epigraphRead O locatedRead ∧
                                            Cont locatedRead C filterRead ∧
                                              Cont filterRead N namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory filterRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro fields wUnary rUnary eUnary oUnary cUnary nUnary windowRoute epigraphRoute
    locatedRoute filterRoute namedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed locatedUnary cUnary filterRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed filterUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row C ∨
              hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead C filterRead ∧
                Cont filterRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, filterRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, filterUnary, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
