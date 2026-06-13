import BEDC.Derived.LowerSemicontinuousUp.BaireWindowFactorization

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousBaireWindowRealSealFactorization [AskSetup] [PackageSetup]
    {X F E W R O H C P N baireRead graphRead epigraphRead locatedRead replayRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory F -> UnaryHistory W -> UnaryHistory R -> UnaryHistory E ->
        UnaryHistory O -> UnaryHistory C -> UnaryHistory N ->
          Cont F W baireRead -> Cont baireRead R graphRead ->
            Cont graphRead E epigraphRead -> Cont epigraphRead O locatedRead ->
              Cont locatedRead C replayRead -> Cont replayRead N realSeal ->
                PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                        hsame row O ∨ hsame row C ∨ hsame row N ∨
                          Cont replayRead N realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F W baireRead ∧
                        Cont baireRead R graphRead ∧ Cont graphRead E epigraphRead ∧
                          Cont epigraphRead O locatedRead ∧
                            Cont locatedRead C replayRead ∧ Cont replayRead N realSeal ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields fUnary wUnary rUnary eUnary oUnary cUnary nUnary baireRoute graphRoute
    epigraphRoute locatedRoute replayRoute realSealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed fUnary wUnary baireRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed baireUnary rUnary graphRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed graphUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary cUnary replayRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary nUnary realSealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
            hsame row C ∨ hsame row N ∨ Cont replayRead N realSeal)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont F W baireRead ∧ Cont baireRead R graphRead ∧
            Cont graphRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
              Cont locatedRead C replayRead ∧ Cont replayRead N realSeal ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
                    (Or.inr realSealRoute))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baireRoute, graphRoute, epigraphRoute, locatedRoute, replayRoute,
          realSealRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, realSealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
