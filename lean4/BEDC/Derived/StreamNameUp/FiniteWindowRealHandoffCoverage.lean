import BEDC.Derived.StreamNameUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameFiniteWindowRealHandoffCoverage [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist}
    {packageBundle : ProbeBundle ProbeName} {n ledger sealRow : BHist} {pkg : Pkg} :
    RatStreamNameFiniteWindowClassifier s t window ->
      InBundle n window ->
        UnaryHistory n ->
          Cont (s n) (t n) ledger ->
            Cont ledger n sealRow ->
              PkgSig packageBundle sealRow pkg ->
                RatHistoryClassifier (s n) (t n) ∧
                  UnaryHistory ledger ∧
                    UnaryHistory sealRow ∧
                      Cont (s n) (t n) ledger ∧
                        Cont ledger n sealRow ∧
                          PkgSig packageBundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro classified member nUnary ledgerRoute sealRoute packageSig
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified n member nUnary
  have positiveRows : PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
    RatHistoryClassifier_positive_denominators pointClassified
  have sourceUnary : UnaryHistory (s n) :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveRows.left).left
  have targetUnary : UnaryHistory (t n) :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveRows.right).left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary targetUnary ledgerRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary nUnary sealRoute
  exact And.intro pointClassified
    (And.intro ledgerUnary
      (And.intro sealUnary
        (And.intro ledgerRoute
          (And.intro sealRoute packageSig))))

end BEDC.Derived.StreamNameUp
