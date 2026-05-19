import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamnameRealSealFactorizationBoundary
    {s t : BHist -> BHist} {window : ProbeBundle BHist} {n ledger sealRow : BHist} :
    RatStreamNameFiniteWindowClassifier s t window ->
      InBundle n window ->
        UnaryHistory n ->
          Cont (s n) (t n) ledger ->
            Cont ledger n sealRow ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                  (fun row : BHist => hsame row sealRow)
                  (fun row : BHist => hsame row sealRow ∧ Cont ledger n sealRow)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont SemanticNameCert hsame
  intro finiteWindow member nUnary ledgerRoute sealRoute
  have selected : RatHistoryClassifier (s n) (t n) :=
    finiteWindow n member nUnary
  have sourceUnary : UnaryHistory (s n) :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp selected.left)).left
  have targetUnary : UnaryHistory (t n) :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp selected.right.left)).left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary targetUnary ledgerRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary nUnary sealRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow ⟨hsame_refl sealRow, sealUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute⟩
  }

theorem StreamNameRealSealFactorizationBoundary [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist} {bundle : ProbeBundle ProbeName}
    {left right dyadicLedger handoff regseqSeal realRead : BHist} {pkg : Pkg} :
    RatStreamNameFiniteWindowClassifier s t window ->
      InBundle left window ->
        InBundle right window ->
          UnaryHistory left ->
            UnaryHistory right ->
              UnaryHistory dyadicLedger ->
                UnaryHistory regseqSeal ->
                  hsame dyadicLedger (append left right) ->
                    Cont (s left) (t right) handoff ->
                      Cont handoff regseqSeal realRead ->
                        PkgSig bundle realRead pkg ->
                          RatHistoryClassifier (s left) (t left) ∧
                            RatHistoryClassifier (s right) (t right) ∧
                              UnaryHistory dyadicLedger ∧ UnaryHistory handoff ∧
                                UnaryHistory realRead ∧ hsame dyadicLedger (append left right) ∧
                                  Cont (s left) (t right) handoff ∧
                                    Cont handoff regseqSeal realRead ∧
                                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame
  intro finiteWindow leftMember rightMember leftUnary rightUnary dyadicUnary regseqUnary
    sameDyadic handoffRoute realRoute pkgRow
  have leftClassified : RatHistoryClassifier (s left) (t left) :=
    finiteWindow left leftMember leftUnary
  have rightClassified : RatHistoryClassifier (s right) (t right) :=
    finiteWindow right rightMember rightUnary
  have sLeftPositive : PositiveUnaryDenominator (s left) :=
    (RatHistoryClassifier_positive_denominators leftClassified).left
  have tRightPositive : PositiveUnaryDenominator (t right) :=
    (RatHistoryClassifier_positive_denominators rightClassified).right
  have sLeftUnary : UnaryHistory (s left) :=
    (PositiveUnaryDenominator_unary_and_nonempty sLeftPositive).left
  have tRightUnary : UnaryHistory (t right) :=
    (PositiveUnaryDenominator_unary_and_nonempty tRightPositive).left
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sLeftUnary tRightUnary handoffRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed handoffUnary regseqUnary realRoute
  exact
    ⟨leftClassified, rightClassified, dyadicUnary, handoffUnary, realUnary, sameDyadic,
      handoffRoute, realRoute, pkgRow⟩

end BEDC.Derived.StreamNameUp
