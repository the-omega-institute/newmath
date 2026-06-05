import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphCarrierScope [AskSetup] [PackageSetup]
    {X F E W R O H C P N lowerRead epigraphRead locatedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont W R lowerRead →
                      Cont lowerRead E epigraphRead →
                        Cont epigraphRead O locatedRead →
                          Cont locatedRead C replayRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row F ∨ hsame row W ∨
                                        hsame row R ∨ hsame row E ∨ hsame row O ∨
                                          hsame row H ∨ hsame row C ∨ hsame row P ∨
                                            hsame row N ∨ hsame row replayRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W R lowerRead ∧
                                        Cont lowerRead E epigraphRead ∧
                                          Cont epigraphRead O locatedRead ∧
                                            Cont locatedRead C replayRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory lowerRead ∧ UnaryHistory epigraphRead ∧
                                    UnaryHistory locatedRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary _hUnary cUnary _nUnary lowerRoute epigraphRoute
    locatedRoute replayRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary rUnary lowerRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed lowerUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R lowerRead ∧ Cont lowerRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead C replayRead ∧
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
        ⟨source.right, lowerRoute, epigraphRoute, locatedRoute, replayRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, lowerUnary, epigraphUnary, locatedUnary, replayUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
