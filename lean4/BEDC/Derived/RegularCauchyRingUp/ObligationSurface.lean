import BEDC.Derived.RegularCauchyRingUp

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRingCarrier_obligation_surface [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S G surface →
        Cont M L surface →
          PkgSig bundle N pkg →
            UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory M ∧ UnaryHistory L ∧
              UnaryHistory surface ∧ Cont S G surface ∧ Cont M L surface ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sumNegSurface productScaleSurface namePkg
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, sUnary, gUnary,
    mUnary, lUnary, _rsUnary, _rgUnary, _rmUnary, _rlUnary, _esUnary, _egUnary,
    _emUnary, _elUnary, _hUnary, _cUnary, _pUnary, _nUnary, _sourceWindowA,
    _sourceWindowB, _transportReplay, provenancePkg, _carrierNamePkg⟩ := carrier
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed sUnary gUnary sumNegSurface
  exact
    ⟨sUnary, gUnary, mUnary, lUnary, surfaceUnary, sumNegSurface, productScaleSurface,
      provenancePkg, namePkg⟩

end BEDC.Derived.RegularCauchyRingUp
