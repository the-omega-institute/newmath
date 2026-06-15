import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootNonescapeStrengthened [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont W R windowRead →
                      Cont windowRead E epigraphRead →
                        Cont epigraphRead O locatedRead →
                          Cont locatedRead H transportRead →
                            Cont transportRead C replayRead →
                              Cont replayRead N namedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row F ∨ hsame row E ∨
                                            hsame row W ∨ hsame row R ∨ hsame row O ∨
                                              hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                hsame row N ∨ hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont W R windowRead ∧
                                            Cont windowRead E epigraphRead ∧
                                              Cont epigraphRead O locatedRead ∧
                                                Cont locatedRead H transportRead ∧
                                                  Cont transportRead C replayRead ∧
                                                    Cont replayRead N namedRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro rootFields windowUnary regularUnary epigraphUnary locatedUnary transportUnary
    replayUnary nameUnary windowRoute epigraphRoute locatedRoute transportRoute replayRoute
    namedRoute provenancePkg namePkg
  have _acceptedRootFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := rootFields
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary regularUnary windowRoute
  have epigraphReadUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowReadUnary epigraphUnary epigraphRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphReadUnary locatedUnary locatedRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedReadUnary transportUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary replayUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨ hsame row R ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C replayRead ∧ Cont replayRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
          namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, namedReadUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
