import BEDC.Derived.LowerSemicontinuousUp.EpigraphThresholdMonotonicity

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphThresholdRefinement [AskSetup] [PackageSetup]
    {q Eq Oq Bq Hq Cq Pq Nq thresholdRead boundaryRead stableRead replayRead refinedRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousSuperlevelThresholdSurface q Eq Oq Bq Hq Cq Pq Nq =
        [q, Eq, Oq, Bq, Hq, Cq, Pq, Nq] →
      UnaryHistory q →
        UnaryHistory Eq →
          UnaryHistory Oq →
            UnaryHistory Bq →
              UnaryHistory Hq →
                UnaryHistory Cq →
                  UnaryHistory Nq →
                    Cont q Eq thresholdRead →
                      Cont thresholdRead Oq boundaryRead →
                        Cont boundaryRead Bq stableRead →
                          Cont stableRead Hq replayRead →
                            Cont replayRead Cq refinedRead →
                              Cont refinedRead Nq sealRead →
                                PkgSig bundle Pq pkg →
                                  PkgSig bundle Nq pkg →
                                    SemanticNameCert
                                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨
                                            hsame row Bq ∨ hsame row Hq ∨ hsame row Cq ∨
                                              hsame row refinedRead ∨ hsame row sealRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont q Eq thresholdRead ∧
                                            Cont thresholdRead Oq boundaryRead ∧
                                              Cont boundaryRead Bq stableRead ∧
                                                Cont stableRead Hq replayRead ∧
                                                  Cont replayRead Cq refinedRead ∧
                                                    Cont refinedRead Nq sealRead ∧
                                                      PkgSig bundle Pq pkg ∧
                                                        PkgSig bundle Nq pkg)
                                        hsame ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldRows qUnary eqUnary oqUnary bqUnary hqUnary cqUnary nqUnary thresholdRoute
    boundaryRoute stableRoute replayRoute refinedRoute sealRoute pPkg nPkg
  cases fieldRows
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed qUnary eqUnary thresholdRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed thresholdUnary oqUnary boundaryRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed boundaryUnary bqUnary stableRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed stableUnary hqUnary replayRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed replayUnary cqUnary refinedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed refinedUnary nqUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨ hsame row Bq ∨
              hsame row Hq ∨ hsame row Cq ∨ hsame row refinedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q Eq thresholdRead ∧
              Cont thresholdRead Oq boundaryRead ∧ Cont boundaryRead Bq stableRead ∧
                Cont stableRead Hq replayRead ∧ Cont replayRead Cq refinedRead ∧
                  Cont refinedRead Nq sealRead ∧ PkgSig bundle Pq pkg ∧
                    PkgSig bundle Nq pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, boundaryRoute, stableRoute, replayRoute, refinedRoute,
          sealRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
