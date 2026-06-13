import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousPublicEpigraphExportRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N baireRead graphRead epigraphRead locatedRead transportRead
      replayRead realSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory X -> UnaryHistory F -> UnaryHistory W -> UnaryHistory R ->
        UnaryHistory E -> UnaryHistory O -> UnaryHistory H -> UnaryHistory C ->
          UnaryHistory P -> UnaryHistory N -> Cont F W baireRead ->
            Cont baireRead R graphRead -> Cont graphRead E epigraphRead ->
              Cont epigraphRead O locatedRead -> Cont locatedRead H transportRead ->
                Cont transportRead C replayRead -> Cont replayRead N realSeal ->
                  Cont realSeal P publicRead -> PkgSig bundle P pkg ->
                    PkgSig bundle N pkg -> PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨
                              hsame row E ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont F W baireRead ∧
                              Cont baireRead R graphRead ∧ Cont graphRead E epigraphRead ∧
                                Cont epigraphRead O locatedRead ∧
                                  Cont locatedRead H transportRead ∧
                                    Cont transportRead C replayRead ∧
                                      Cont replayRead N realSeal ∧
                                        Cont realSeal P publicRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                            PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory baireRead ∧ UnaryHistory graphRead ∧
                          UnaryHistory epigraphRead ∧ UnaryHistory locatedRead ∧
                            UnaryHistory transportRead ∧ UnaryHistory replayRead ∧
                              UnaryHistory realSeal ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields epigraphFields _xUnary fUnary wUnary rUnary eUnary oUnary hUnary cUnary
    pUnary nUnary baireRoute graphRoute epigraphRoute locatedRoute transportRoute
    replayRoute sealRoute publicRoute pPkg nPkg publicPkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed fUnary wUnary baireRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed baireUnary rUnary graphRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed graphUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary nUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realSealUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F W baireRead ∧ Cont baireRead R graphRead ∧
              Cont graphRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                Cont locatedRead H transportRead ∧ Cont transportRead C replayRead ∧
                  Cont replayRead N realSeal ∧ Cont realSeal P publicRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baireRoute, graphRoute, epigraphRoute, locatedRoute, transportRoute,
          replayRoute, sealRoute, publicRoute, pPkg, nPkg, publicPkg⟩
  }
  exact
    ⟨cert, baireUnary, graphUnary, epigraphUnary, locatedUnary, transportUnary, replayUnary,
      realSealUnary, publicUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
