import BEDC.Derived.NormalFormConsistencySealUp.CriticalPairRoute

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMatureTreatment [AskSetup] [PackageSetup]
    {T F N K X H C P L candidateRead closedRead residualRead scheduleRead
      handoffRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    normalFormConsistencySealFields (NormalFormConsistencySealUp.mk T F N K X H C P L) =
        [T, F, N, K, X, H, C, P, L] ->
      UnaryHistory T ->
        UnaryHistory F ->
          UnaryHistory N ->
            UnaryHistory K ->
              UnaryHistory X ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory L ->
                        Cont T F candidateRead ->
                          Cont N K closedRead ->
                            Cont candidateRead closedRead residualRead ->
                              Cont residualRead H scheduleRead ->
                                Cont scheduleRead C handoffRead ->
                                  Cont handoffRead L matureRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle L pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row matureRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row T ∨ hsame row F ∨ hsame row N ∨
                                                hsame row K ∨ hsame row X ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨
                                                    hsame row L ∨ hsame row matureRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont handoffRead L matureRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle L pkg)
                                            hsame ∧
                                          UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: NormalFormConsistencySealUp BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldsExact unaryT unaryF unaryN unaryK _unaryX unaryH unaryC _unaryP unaryL
    candidateRoute closedRoute residualRoute scheduleRoute handoffRoute matureRoute
    provenancePkg localNamePkg
  cases fieldsExact
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed unaryT unaryF candidateRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed unaryN unaryK closedRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary closedUnary residualRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed residualUnary unaryH scheduleRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed scheduleUnary unaryC handoffRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed handoffUnary unaryL matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoffRead L matureRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, matureRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, matureUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
