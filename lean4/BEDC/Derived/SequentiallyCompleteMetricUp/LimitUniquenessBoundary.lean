import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricLimitUniquenessBoundary [AskSetup] [PackageSetup]
    {X S M L D L' D' H C P N compareRead compareRead' boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory L' ->
                  UnaryHistory D' ->
                    UnaryHistory C ->
                      Cont S M compareRead ->
                        Cont compareRead L boundaryRead ->
                          Cont compareRead L' compareRead' ->
                            hsame D D' ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row boundaryRead ∨ hsame row compareRead') ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row S ∨ hsame row M ∨
                                          hsame row L ∨ hsame row L' ∨ hsame row D ∨
                                            hsame row D' ∨ Cont S M compareRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont S M compareRead ∧
                                          Cont compareRead L boundaryRead ∧
                                            Cont compareRead L' compareRead' ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory boundaryRead ∧ UnaryHistory compareRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows _xUnary sUnary mUnary lUnary _dUnary l'Unary _d'Unary _cUnary
    compareRoute boundaryRoute compareRoute' _sameLedger provenancePkg namePkg
  cases fieldRows
  have compareUnary : UnaryHistory compareRead :=
    unary_cont_closed sUnary mUnary compareRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed compareUnary lUnary boundaryRoute
  have compareRead'Unary : UnaryHistory compareRead' :=
    unary_cont_closed compareUnary l'Unary compareRoute'
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro boundaryRead ⟨Or.inl (hsame_refl boundaryRead), boundaryUnary⟩
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
          constructor
          · cases source.left with
            | inl boundarySame =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) boundarySame)
            | inr compareSame =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) compareSame)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr compareRoute))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, compareRoute, boundaryRoute, compareRoute', provenancePkg, namePkg⟩
    }
  · exact ⟨boundaryUnary, compareRead'Unary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
