import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteNetMinimumFoldPacket [AskSetup] [PackageSetup]
    (bundleRow radius accumulator lower transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
    UnaryHistory nameRow ∧
      Cont bundleRow radius transport ∧ Cont transport accumulator lower ∧
        Cont lower route provenance ∧ PkgSig bundle provenance pkg

theorem FiniteNetMinimumFoldPacket_nonempty_probe_exhaustion [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow consumed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg ->
      Cont bundleRow radius consumed ->
        Cont consumed accumulator lower ->
          PkgSig bundle provenance pkg ->
            UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
              UnaryHistory consumed ∧ Cont bundleRow radius consumed ∧
                Cont consumed accumulator lower ∧ PkgSig bundle provenance pkg := by
  intro packet bundleRadiusConsumed consumedAccumulatorLower provenancePkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, _nameRowUnary, _transportRoute,
    _lowerRoute, _provenanceRoute, _packetPkg⟩ := packet
  have consumedUnary : UnaryHistory consumed :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusConsumed
  exact
    ⟨bundleRowUnary, radiusUnary, accumulatorUnary, consumedUnary, bundleRadiusConsumed,
      consumedAccumulatorLower, provenancePkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
