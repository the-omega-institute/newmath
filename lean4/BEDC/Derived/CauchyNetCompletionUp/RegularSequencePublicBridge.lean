import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyNetCompletionRegularSequencePublicBridge [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N schedule regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont W Q schedule ->
        Cont schedule R regularRead ->
          Cont regularRead S sealRead ->
            hsame sealRead A ->
              PkgSig bundle N pkg ->
                Cont W Q schedule ∧ Cont schedule R regularRead ∧
                  Cont regularRead S sealRead ∧ hsame sealRead A ∧
                    PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier scheduleRoute regularRoute sealRoute sealSame _localNamePkg
  obtain ⟨_unaryD, _unaryW, _unaryQ, _unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _directedWindow, _mooreRoute,
      _uniformRoute, _realSealRoute, _provenancePkg, localNamePkg⟩ := carrier
  exact ⟨scheduleRoute, regularRoute, sealRoute, sealSame, localNamePkg⟩

end BEDC.Derived.CauchyNetCompletionUp
