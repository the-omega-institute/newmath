import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_root_window_lock [AskSetup] [PackageSetup]
    {W M Q T S H C P N rootRead sealRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M rootRead ->
        Cont rootRead Q T ->
          Cont T S sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory T ∧
                UnaryHistory S ∧ UnaryHistory rootRead ∧ UnaryHistory sealRead ∧
                  Cont W M rootRead ∧ Cont rootRead Q T ∧ Cont T S sealRead ∧
                    hsame sealRead (append T S) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont hsame ProbeBundle Pkg UnaryHistory
  intro carrier wMRoot rootQT tSSeal sealPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _wMQ, _mQT, _tSC, _cNP, pPkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed wUnary mUnary wMRoot
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary sUnary tSSeal
  exact
    ⟨wUnary, mUnary, qUnary, tUnary, sUnary, rootUnary, sealUnary, wMRoot, rootQT,
      tSSeal, tSSeal, pPkg, sealPkg⟩

end BEDC.Derived.CauchyOscillationUp
