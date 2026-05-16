import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityToleranceLedgerHandoff [AskSetup] [PackageSetup]
    {R T S D W Q L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier R T S D W Q L H C P N bundle pkg ->
      Cont R D budget ->
        Cont budget W tolerance ->
          PkgSig bundle tolerance pkg ->
      UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory D ∧
        UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory L ∧ UnaryHistory H ∧
          UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory budget ∧
            UnaryHistory tolerance ∧
            Cont R T S ∧ Cont D W Q ∧ Cont Q L C ∧ Cont C N H ∧
              Cont R D budget ∧ Cont budget W tolerance ∧
                PkgSig bundle P pkg ∧ PkgSig bundle tolerance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier rDBudget budgetWTolerance tolerancePkg
  obtain ⟨rUnary, tUnary, sUnary, dUnary, wUnary, qUnary, lUnary, hUnary, cUnary,
    pUnary, nUnary, rts, dwq, qlc, cnh, pPkg⟩ := carrier
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed rUnary dUnary rDBudget
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed budgetUnary wUnary budgetWTolerance
  exact
    ⟨rUnary, tUnary, sUnary, dUnary, wUnary, qUnary, lUnary, hUnary, cUnary,
      pUnary, nUnary, budgetUnary, toleranceUnary, rts, dwq, qlc, cnh, rDBudget,
      budgetWTolerance, pPkg, tolerancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
