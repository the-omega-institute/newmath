import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousKernelScope [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead replayRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory F ->
          UnaryHistory W ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory O ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      Cont X W windowRead ->
                        Cont windowRead R epigraphRead ->
                          Cont epigraphRead E locatedRead ->
                            Cont locatedRead O transportRead ->
                              Cont transportRead H replayRead ->
                                Cont replayRead C realSeal ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist => hsame row realSeal ∧
                                            UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row F ∨ hsame row W ∨
                                              hsame row R ∨ hsame row E ∨ hsame row O ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row realSeal)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont X W windowRead ∧
                                              Cont windowRead R epigraphRead ∧
                                                Cont epigraphRead E locatedRead ∧
                                                  Cont locatedRead O transportRead ∧
                                                    Cont transportRead H replayRead ∧
                                                      Cont replayRead C realSeal ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert hsame
  intro fields xUnary _fUnary wUnary rUnary eUnary oUnary hUnary cUnary windowRoute
    epigraphRoute locatedRoute transportRoute replayRoute realSealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary wUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary rUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary eUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary oUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary hUnary replayRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary cUnary realSealRoute
  exact {
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
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, transportRoute, replayRoute,
          realSealRoute, provenancePkg, namePkg⟩
  }

end BEDC.Derived.LowerSemicontinuousUp
