import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphRouteSurface

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphRows [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory C ->
                Cont W R windowRead ->
                  Cont windowRead E epigraphRead ->
                    Cont epigraphRead O locatedRead ->
                      Cont locatedRead C replayRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row W ∨ hsame row R ∨ hsame row E ∨
                                    hsame row O ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W R windowRead ∧
                                    Cont windowRead E epigraphRead ∧
                                      Cont epigraphRead O locatedRead ∧
                                        Cont locatedRead C replayRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                                UnaryHistory locatedRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro epigraphFields windowUnary regularUnary epigraphUnary locatedUnary replayUnary
    windowRoute epigraphRoute locatedRoute replayRoute provenancePkg namePkg
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary regularUnary windowRoute
  have epigraphReadUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowReadUnary epigraphUnary epigraphRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphReadUnary locatedUnary locatedRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedReadUnary replayUnary replayRoute
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead C replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, windowReadUnary, epigraphReadUnary, locatedReadUnary, replayReadUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
