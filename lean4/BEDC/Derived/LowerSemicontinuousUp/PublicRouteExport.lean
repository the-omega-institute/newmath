import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousPublicRouteExport [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead replayRead realSeal
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory C ->
                UnaryHistory N ->
                  UnaryHistory P ->
                    Cont W R windowRead ->
                      Cont windowRead E epigraphRead ->
                        Cont epigraphRead O locatedRead ->
                          Cont locatedRead C replayRead ->
                            Cont replayRead N realSeal ->
                              Cont realSeal P publicRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    PkgSig bundle publicRead pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row publicRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row W ∨ hsame row R ∨ hsame row E ∨
                                              hsame row O ∨ hsame row C ∨ hsame row P ∨
                                                hsame row N ∨ Cont realSeal P publicRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont W R windowRead ∧
                                              Cont windowRead E epigraphRead ∧
                                                Cont epigraphRead O locatedRead ∧
                                                  Cont locatedRead C replayRead ∧
                                                    Cont replayRead N realSeal ∧
                                                      Cont realSeal P publicRead ∧
                                                        PkgSig bundle publicRead pkg)
                                          hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields wUnary rUnary eUnary oUnary cUnary nUnary pUnary windowRoute epigraphRoute
    locatedRoute replayRoute sealRoute publicRoute _provenancePkg _namePkg publicPkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary cUnary replayRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary nUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realSealUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ Cont realSeal P publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead C replayRead ∧
                Cont replayRead N realSeal ∧ Cont realSeal P publicRead ∧
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr publicRoute))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, replayRoute, sealRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
