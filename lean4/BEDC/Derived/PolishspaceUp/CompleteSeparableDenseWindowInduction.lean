import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparableDenseWindowInduction [AskSetup] [PackageSetup]
    {M K D S R W H C G N : BHist} {denseWindow readbackWindow : Nat → BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K (denseWindow 0) →
        (∀ n : Nat, Cont (denseWindow n) S (denseWindow (Nat.succ n))) →
          (∀ n : Nat, Cont (denseWindow n) R (readbackWindow n)) →
            (∀ n : Nat, PkgSig bundle (readbackWindow n) pkg) →
              ∀ n : Nat,
                UnaryHistory (denseWindow n) ∧ UnaryHistory (readbackWindow n) ∧
                  PkgSig bundle (readbackWindow n) pkg := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier baseWindow successorWindow readbackRoute readbackPkg n
  obtain ⟨MUnary, KUnary, _DUnary, SUnary, RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  induction n with
  | zero =>
      have denseUnary : UnaryHistory (denseWindow 0) :=
        unary_cont_closed MUnary KUnary baseWindow
      have readbackUnary : UnaryHistory (readbackWindow 0) :=
        unary_cont_closed denseUnary RUnary (readbackRoute 0)
      exact ⟨denseUnary, readbackUnary, readbackPkg 0⟩
  | succ n ih =>
      have denseUnary : UnaryHistory (denseWindow (Nat.succ n)) :=
        unary_cont_closed ih.left SUnary (successorWindow n)
      have readbackUnary : UnaryHistory (readbackWindow (Nat.succ n)) :=
        unary_cont_closed denseUnary RUnary (readbackRoute (Nat.succ n))
      exact ⟨denseUnary, readbackUnary, readbackPkg (Nat.succ n)⟩

end BEDC.Derived.PolishspaceUp
