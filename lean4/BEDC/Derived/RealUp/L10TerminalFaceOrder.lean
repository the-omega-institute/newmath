import BEDC.Derived.RealUp.L10DependencyLattice

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10TerminalFaceOrder [AskSetup] [PackageSetup]
    {dyadic stream regular realSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        UnaryHistory regular ->
          UnaryHistory realSeal ->
            Cont dyadic stream regular ->
              Cont regular realSeal terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory terminal ∧ Cont dyadic stream regular ∧
                    Cont regular realSeal terminal ∧ PkgSig bundle terminal pkg ∧
                      hsame terminal terminal := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro _dyadicUnary _streamUnary regularUnary realSealUnary dyadicStreamRegular
    regularRealSealTerminal terminalPkg
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed regularUnary realSealUnary regularRealSealTerminal
  exact
    ⟨terminalUnary, dyadicStreamRegular, regularRealSealTerminal, terminalPkg,
      hsame_refl terminal⟩

end BEDC.Derived.RealUp
