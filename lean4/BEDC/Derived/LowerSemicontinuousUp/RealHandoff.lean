import BEDC.Derived.LowerSemicontinuousUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def lowerSemicontinuousRootFields : LowerSemicontinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerSemicontinuousUp.mk X F E W R O H C P N => [X, F, E, W, R, O, H, C, P, N]

theorem LowerSemicontinuousReal_handoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              Cont W R windowRead ->
                Cont windowRead E epigraphRead ->
                  Cont epigraphRead O realSeal ->
                    PkgSig bundle P pkg ->
                      UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                        UnaryHistory realSeal ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                                Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
                                  Cont epigraphRead O realSeal)
                            (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields rowsW rowsR rowsE rowsO windowRoute epigraphRoute realSealRoute packageRead
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rowsW rowsR windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary rowsE epigraphRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed epigraphUnary rowsO realSealRoute
  have sourceAtSeal : hsame realSeal realSeal ∧ UnaryHistory realSeal :=
    ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
            Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
              Cont epigraphRead O realSeal)
        (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realSealRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨packageRead, source.left⟩
  }
  exact ⟨windowUnary, epigraphUnary, realSealUnary, cert⟩

theorem LowerSemicontinuousRoot_epigraph_carrier [AskSetup] [PackageSetup]
    {X F E W R O H C P N valueRead epigraphRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory F ->
          UnaryHistory E ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory O ->
                  Cont W R valueRead ->
                    Cont valueRead E epigraphRead ->
                      Cont epigraphRead O locatedRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row F ∨ hsame row E ∨
                                    hsame row W ∨ hsame row R ∨ hsame row O ∨
                                      hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row valueRead ∨
                                          hsame row epigraphRead ∨ hsame row locatedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W R valueRead ∧
                                    Cont valueRead E epigraphRead ∧
                                      Cont epigraphRead O locatedRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory valueRead ∧ UnaryHistory epigraphRead ∧
                                UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields _xUnary _fUnary eUnary wUnary rUnary oUnary valueRoute epigraphRoute
    locatedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed wUnary rUnary valueRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed valueUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨ hsame row R ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row valueRead ∨ hsame row epigraphRead ∨ hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R valueRead ∧ Cont valueRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead
        ⟨hsame_refl locatedRead, locatedUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, valueRoute, epigraphRoute, locatedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, valueUnary, epigraphUnary, locatedUnary⟩

theorem LowerSemicontinuousClosedSuperlevel_stability [AskSetup] [PackageSetup]
    {q Eq Oq Bq Hq Cq Pq Nq thresholdRead boundaryRead stableRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q ->
      UnaryHistory Eq ->
        UnaryHistory Oq ->
          UnaryHistory Bq ->
            UnaryHistory Hq ->
              Cont q Eq thresholdRead ->
                Cont thresholdRead Oq boundaryRead ->
                  Cont boundaryRead Bq stableRead ->
                    Cont stableRead Hq replayRead ->
                      PkgSig bundle Pq pkg ->
                        PkgSig bundle Nq pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨
                                  hsame row Bq ∨ hsame row Hq ∨ hsame row Cq ∨
                                    hsame row Pq ∨ hsame row Nq ∨ hsame row thresholdRead ∨
                                      hsame row boundaryRead ∨ hsame row stableRead ∨
                                        hsame row replayRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont q Eq thresholdRead ∧
                                  Cont thresholdRead Oq boundaryRead ∧
                                    Cont boundaryRead Bq stableRead ∧
                                      Cont stableRead Hq replayRead ∧
                                        PkgSig bundle Pq pkg ∧ PkgSig bundle Nq pkg)
                              hsame ∧
                            UnaryHistory thresholdRead ∧ UnaryHistory boundaryRead ∧
                              UnaryHistory stableRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro qUnary eqUnary oqUnary bqUnary hqUnary thresholdRoute boundaryRoute stableRoute
    replayRoute provenancePkg namePkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed qUnary eqUnary thresholdRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed thresholdUnary oqUnary boundaryRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed boundaryUnary bqUnary stableRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed stableUnary hqUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨ hsame row Bq ∨ hsame row Hq ∨
              hsame row Cq ∨ hsame row Pq ∨ hsame row Nq ∨ hsame row thresholdRead ∨
                hsame row boundaryRead ∨ hsame row stableRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q Eq thresholdRead ∧ Cont thresholdRead Oq boundaryRead ∧
              Cont boundaryRead Bq stableRead ∧ Cont stableRead Hq replayRead ∧
                PkgSig bundle Pq pkg ∧ PkgSig bundle Nq pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, boundaryRoute, stableRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, thresholdUnary, boundaryUnary, stableUnary, replayUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
