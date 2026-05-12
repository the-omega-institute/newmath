import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicRoundingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicRoundingPacket [AskSetup] [PackageSetup]
    (source precision left right interval budget transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory precision ∧ UnaryHistory left ∧ UnaryHistory right ∧
    UnaryHistory interval ∧ UnaryHistory budget ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont source precision interval ∧
        Cont interval budget provenance ∧ PkgSig bundle cert pkg

theorem DyadicRoundingPacket_grid_sandwich [AskSetup] [PackageSetup]
    {source precision left right interval budget transport route provenance cert sandwich : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingPacket source precision left right interval budget transport route provenance cert
        bundle pkg ->
      Cont left interval sandwich ->
        Cont sandwich right budget ->
          UnaryHistory precision ∧ UnaryHistory left ∧ UnaryHistory right ∧
            UnaryHistory interval ∧ UnaryHistory budget ∧ Cont left interval sandwich ∧
              Cont sandwich right budget ∧ PkgSig bundle cert pkg := by
  intro packet leftInterval rightBudget
  obtain ⟨_sourceUnary, precisionUnary, leftUnary, rightUnary, intervalUnary, budgetUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _sourceInterval,
    _intervalProvenance, certSig⟩ := packet
  exact
    ⟨precisionUnary, leftUnary, rightUnary, intervalUnary, budgetUnary, leftInterval,
      rightBudget, certSig⟩

end BEDC.Derived.DyadicRoundingUp
