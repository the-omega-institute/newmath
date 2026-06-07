import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousClosedSuperlevelCarrier_surface [AskSetup] [PackageSetup]
    {X F E W R O H C P N q Eq Oq Bq _Hq _Cq Pq Nq thresholdRead boundaryRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory q ->
        UnaryHistory Eq ->
          UnaryHistory Oq ->
            UnaryHistory Bq ->
              UnaryHistory Nq ->
                Cont Eq Oq thresholdRead ->
                  Cont thresholdRead Bq boundaryRead ->
                    Cont boundaryRead Nq namedRead ->
                      PkgSig bundle Pq pkg ->
                        PkgSig bundle Nq pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨
                                  hsame row Bq ∨ hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Eq Oq thresholdRead ∧
                                  Cont thresholdRead Bq boundaryRead ∧
                                    Cont boundaryRead Nq namedRead ∧ PkgSig bundle Nq pkg)
                              hsame ∧
                            UnaryHistory thresholdRead ∧ UnaryHistory boundaryRead ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rootFields _qUnary eqUnary oqUnary bqUnary nqUnary thresholdRoute boundaryRoute
    namedRoute _thresholdPkg namedPkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := rootFields
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed eqUnary oqUnary thresholdRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed thresholdUnary bqUnary boundaryRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed boundaryUnary nqUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨ hsame row Bq ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Eq Oq thresholdRead ∧
              Cont thresholdRead Bq boundaryRead ∧ Cont boundaryRead Nq namedRead ∧
                PkgSig bundle Nq pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdRoute, boundaryRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, thresholdUnary, boundaryUnary, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
