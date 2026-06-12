import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousOpenSublevelRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N valueRead epigraphRead locatedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory O ->
                UnaryHistory H ->
                  Cont X W valueRead ->
                    Cont valueRead R epigraphRead ->
                      Cont epigraphRead E locatedRead ->
                        Cont locatedRead O replayRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row X ∨ hsame row W ∨ hsame row R ∨
                                      hsame row E ∨ hsame row O ∨ hsame row replayRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont X W valueRead ∧
                                      Cont valueRead R epigraphRead ∧
                                        Cont epigraphRead E locatedRead ∧
                                          Cont locatedRead O replayRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory valueRead ∧ UnaryHistory epigraphRead ∧
                                  UnaryHistory locatedRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory hsame
  intro fields xUnary wUnary rUnary eUnary oUnary _hUnary valueRoute epigraphRoute
    locatedRoute replayRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed xUnary wUnary valueRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed valueUnary rUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary eUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary oUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W valueRead ∧ Cont valueRead R epigraphRead ∧
              Cont epigraphRead E locatedRead ∧ Cont locatedRead O replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        ⟨source.right, valueRoute, epigraphRoute, locatedRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, valueUnary, epigraphUnary, locatedUnary, replayUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
