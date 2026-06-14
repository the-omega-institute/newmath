import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousFormalTargetBridgeRequest [AskSetup] [PackageSetup]
    {X F E W R O H C P N thresholdRead locatedRead transportRead replayRead namedRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont W R thresholdRead →
                        Cont thresholdRead E locatedRead →
                          Cont locatedRead O transportRead →
                            Cont transportRead H replayRead →
                              Cont replayRead C namedRead →
                                Cont namedRead P publicRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row publicRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row W ∨ hsame row R ∨ hsame row E ∨
                                              hsame row O ∨ hsame row H ∨ hsame row C ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row publicRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont W R thresholdRead ∧
                                              Cont thresholdRead E locatedRead ∧
                                                Cont locatedRead O transportRead ∧
                                                  Cont transportRead H replayRead ∧
                                                    Cont replayRead C namedRead ∧
                                                      Cont namedRead P publicRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro epigraphFields windowUnary regularUnary epigraphUnary locatedUnary transportUnary
    replayUnary provenanceUnary nameUnary thresholdRoute locatedRoute transportRoute
    replayRoute namedRoute publicRoute provenancePkg namePkg
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary regularUnary thresholdRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed thresholdUnary epigraphUnary locatedRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedReadUnary locatedUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary transportUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary replayUnary namedRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed namedReadUnary provenanceUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R thresholdRead ∧ Cont thresholdRead E locatedRead ∧
              Cont locatedRead O transportRead ∧ Cont transportRead H replayRead ∧
                Cont replayRead C namedRead ∧ Cont namedRead P publicRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, locatedRoute, transportRoute, replayRoute,
          namedRoute, publicRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
