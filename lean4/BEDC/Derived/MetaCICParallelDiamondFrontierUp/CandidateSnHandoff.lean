import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierCandidateSnHandoff [AskSetup] [PackageSetup]
    {P K J R S C B O H T G N premiseRead candidateRead frontierRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory P →
      UnaryHistory K →
        UnaryHistory J →
          UnaryHistory R →
            UnaryHistory S →
              UnaryHistory C →
                UnaryHistory B →
                  UnaryHistory O →
                    UnaryHistory H →
                      Cont P K premiseRead →
                        Cont premiseRead J candidateRead →
                          Cont candidateRead R frontierRead →
                            Cont H frontierRead named →
                              PkgSig bundle named pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row named ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row P ∨ hsame row K ∨ hsame row J ∨
                                        hsame row R ∨ hsame row S ∨ hsame row C ∨
                                          hsame row B ∨ hsame row O ∨ hsame row H ∨
                                            hsame row T ∨ hsame row G ∨ hsame row N ∨
                                              hsame row named)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont P K premiseRead ∧
                                        Cont premiseRead J candidateRead ∧
                                          Cont candidateRead R frontierRead ∧
                                            Cont H frontierRead named ∧
                                              PkgSig bundle named pkg)
                                    hsame ∧
                                  UnaryHistory premiseRead ∧ UnaryHistory candidateRead ∧
                                    UnaryHistory frontierRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro pUnary kUnary jUnary rUnary _sUnary _cUnary _bUnary _oUnary hUnary premiseRoute
    candidateRoute frontierRoute namedRoute namedPkg
  have premiseReadUnary : UnaryHistory premiseRead :=
    unary_cont_closed pUnary kUnary premiseRoute
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed premiseReadUnary jUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary rUnary frontierRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary frontierReadUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row K ∨ hsame row J ∨ hsame row R ∨ hsame row S ∨
              hsame row C ∨ hsame row B ∨ hsame row O ∨ hsame row H ∨ hsame row T ∨
                hsame row G ∨ hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P K premiseRead ∧ Cont premiseRead J candidateRead ∧
              Cont candidateRead R frontierRead ∧ Cont H frontierRead named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                          (Or.inr
                            (Or.inr
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, premiseRoute, candidateRoute, frontierRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, premiseReadUnary, candidateReadUnary, frontierReadUnary, namedUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
