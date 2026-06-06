import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphWindowMonotoneRefinement [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead refinedWindow epigraphRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              Cont W R windowRead ->
                Cont windowRead R refinedWindow ->
                  Cont refinedWindow E epigraphRead ->
                    Cont epigraphRead O locatedRead ->
                      PkgSig bundle P pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                                Cont W R windowRead ∨ Cont windowRead R refinedWindow ∨
                                  Cont refinedWindow E epigraphRead ∨
                                    Cont epigraphRead O locatedRead)
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory refinedWindow ∧ UnaryHistory epigraphRead ∧
                            UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows wUnary rUnary eUnary oUnary windowRoute refinedRoute epigraphRoute
    locatedRoute provenancePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed windowUnary rUnary refinedRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed refinedUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              Cont W R windowRead ∨ Cont windowRead R refinedWindow ∨
                Cont refinedWindow E epigraphRead ∨ Cont epigraphRead O locatedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedUnary⟩
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr locatedRoute))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }
  exact ⟨cert, refinedUnary, epigraphUnary, locatedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
