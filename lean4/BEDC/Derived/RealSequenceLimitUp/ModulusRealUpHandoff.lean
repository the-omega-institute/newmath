import BEDC.Derived.RealSequenceLimitUp.ModulusExtraction

namespace BEDC.Derived.RealSequenceLimitUp.ModulusRealUpHandoff

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitModulusRealUp_handoff [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont dyadicLedger windowSchedule threshold ->
        Cont threshold classifierRow admitted ->
          Cont admitted realSeal route ->
            PkgSig bundle admitted pkg ->
              UnaryHistory dyadicLedger ∧ UnaryHistory windowSchedule ∧
                UnaryHistory threshold ∧ UnaryHistory classifierRow ∧ UnaryHistory admitted ∧
                  Cont dyadicLedger windowSchedule threshold ∧
                    Cont threshold classifierRow admitted ∧ Cont admitted realSeal route ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle admitted pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier thresholdCont admittedCont realSealCont admittedPkg
  have extracted :=
    RealSequenceLimitModulusExtraction carrier thresholdCont admittedCont admittedPkg
  exact
    ⟨extracted.left, extracted.right.left, extracted.right.right.left,
      extracted.right.right.right.left, extracted.right.right.right.right.left,
      extracted.right.right.right.right.right.left,
      extracted.right.right.right.right.right.right.left, realSealCont,
      extracted.right.right.right.right.right.right.right.left,
      extracted.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RealSequenceLimitUp.ModulusRealUpHandoff
