import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PackingNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PackingNumberCarrier [AskSetup] [PackageSetup]
    (X eps U D B H C P N separatedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
    UnaryHistory B ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory separatedRead ∧ Cont X U separatedRead ∧
        PkgSig bundle P pkg

theorem PackingNumberCoveringDualHandoff [AskSetup] [PackageSetup]
    {X eps U D B H C P N separatedRead coveringRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackingNumberCarrier X eps U D B H C P N separatedRead bundle pkg →
      Cont separatedRead B coveringRead →
        PkgSig bundle coveringRead pkg →
          UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
            UnaryHistory B ∧ UnaryHistory separatedRead ∧ UnaryHistory coveringRead ∧
              Cont X U separatedRead ∧ Cont separatedRead B coveringRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle coveringRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier separatedCovering coveringPkg
  obtain ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, separatedUnary, sourceCentersSeparated, provenancePkg⟩ := carrier
  have coveringUnary : UnaryHistory coveringRead :=
    unary_cont_closed separatedUnary bUnary separatedCovering
  exact
    ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, separatedUnary, coveringUnary,
      sourceCentersSeparated, separatedCovering, provenancePkg, coveringPkg⟩

end BEDC.Derived.PackingNumberUp
