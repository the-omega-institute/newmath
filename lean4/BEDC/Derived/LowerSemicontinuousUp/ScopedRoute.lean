import BEDC.Derived.LowerSemicontinuousUp.ObligationClosurePackage

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousScopedRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead readbackRead epigraphRead locatedRead replayRead
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory O →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont X W windowRead →
                      Cont windowRead R readbackRead →
                        Cont readbackRead E epigraphRead →
                          Cont epigraphRead O locatedRead →
                            Cont locatedRead C replayRead →
                              Cont replayRead N scopedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row scopedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row W ∨ hsame row R ∨
                                            hsame row E ∨ hsame row O ∨ hsame row C ∨
                                              hsame row N ∨ hsame row scopedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont X W windowRead ∧
                                            Cont windowRead R readbackRead ∧
                                              Cont readbackRead E epigraphRead ∧
                                                Cont epigraphRead O locatedRead ∧
                                                  Cont locatedRead C replayRead ∧
                                                    Cont replayRead N scopedRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                                        UnaryHistory epigraphRead ∧ UnaryHistory locatedRead ∧
                                          UnaryHistory replayRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro fields xUnary wUnary rUnary eUnary oUnary cUnary nUnary windowRoute readbackRoute
    epigraphRoute locatedRoute replayRoute scopedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary cUnary replayRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed replayUnary nUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              hsame row C ∨ hsame row N ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W windowRead ∧ Cont windowRead R readbackRead ∧
              Cont readbackRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                Cont locatedRead C replayRead ∧ Cont replayRead N scopedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
        ⟨source.right, windowRoute, readbackRoute, epigraphRoute, locatedRoute, replayRoute,
          scopedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, windowUnary, readbackUnary, epigraphUnary, locatedUnary, replayUnary, scopedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
