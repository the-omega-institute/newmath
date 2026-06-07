import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationRegSeqRatUniformThreshold [AskSetup] [PackageSetup]
    {W M Q T S H C P N thresholdRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg →
      Cont W M thresholdRead →
        Cont thresholdRead Q toleranceRead →
          Cont toleranceRead S sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory T ∧
                UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                  UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory sealRead ∧ Cont W M thresholdRead ∧
                      Cont thresholdRead Q toleranceRead ∧ Cont toleranceRead S sealRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier thresholdRoute toleranceRoute sealRoute sealPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, sUnary, hUnary, cUnary, pUnary, nUnary,
    _wMRoute, _mQRoute, _tSRoute, _cNRoute, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed wUnary mUnary thresholdRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary sUnary sealRoute
  exact
    ⟨wUnary, mUnary, qUnary, tUnary, hUnary, cUnary, pUnary, nUnary, thresholdUnary,
      toleranceUnary, sealUnary, thresholdRoute, toleranceRoute, sealRoute, provenancePkg,
      sealPkg⟩

end BEDC.Derived.CauchyOscillationUp
