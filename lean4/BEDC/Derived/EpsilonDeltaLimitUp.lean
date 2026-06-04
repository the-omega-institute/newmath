import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EpsilonDeltaLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EpsilonDeltaLimitCarrier [AskSetup] [PackageSetup]
    (X Y a L E D W R H C P N epsilonRead deltaRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory a ∧ UnaryHistory L ∧
    UnaryHistory E ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        UnaryHistory epsilonRead ∧ UnaryHistory deltaRead ∧ Cont X E epsilonRead ∧
          Cont epsilonRead D deltaRead ∧ PkgSig bundle P pkg

theorem EpsilonDeltaLimitRealSealNonescape [AskSetup] [PackageSetup]
    {X Y a L E D W R H C P N epsilonRead deltaRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpsilonDeltaLimitCarrier X Y a L E D W R H C P N epsilonRead deltaRead
        bundle pkg →
      Cont deltaRead R sealRead →
        PkgSig bundle sealRead pkg →
          UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory E ∧ UnaryHistory D ∧
            UnaryHistory epsilonRead ∧ UnaryHistory deltaRead ∧ UnaryHistory sealRead ∧
              Cont X E epsilonRead ∧ Cont epsilonRead D deltaRead ∧
                Cont deltaRead R sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier deltaRealSeal sealPkg
  obtain ⟨xUnary, yUnary, _aUnary, _lUnary, eUnary, dUnary, _wUnary, rUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, epsilonUnary, deltaUnary, sourceEpsilon,
    epsilonDelta, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed deltaUnary rUnary deltaRealSeal
  exact
    ⟨xUnary, yUnary, eUnary, dUnary, epsilonUnary, deltaUnary, sealUnary,
      sourceEpsilon, epsilonDelta, deltaRealSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.EpsilonDeltaLimitUp
