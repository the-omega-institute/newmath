import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryKernelDependencyRoute [AskSetup] [PackageSetup]
    {e a t v h c p n negativeRead hostLeakageRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont e a negativeRead →
        Cont negativeRead t hostLeakageRead →
          Cont hostLeakageRead h transportRead →
            PkgSig bundle negativeRead pkg →
              PkgSig bundle hostLeakageRead pkg →
                PkgSig bundle transportRead pkg →
                  UnaryHistory negativeRead ∧ UnaryHistory hostLeakageRead ∧
                    UnaryHistory transportRead ∧ Cont e a negativeRead ∧
                      Cont negativeRead t hostLeakageRead ∧
                        Cont hostLeakageRead h transportRead ∧
                          PkgSig bundle negativeRead pkg ∧
                            PkgSig bundle hostLeakageRead pkg ∧
                              PkgSig bundle transportRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eANegative negativeTHost hostHTransport negativePkg hostPkg transportPkg
  obtain ⟨eUnary, aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have negativeUnary : UnaryHistory negativeRead :=
    unary_cont_closed eUnary aUnary eANegative
  have hostUnary : UnaryHistory hostLeakageRead :=
    unary_cont_closed negativeUnary tUnary negativeTHost
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed hostUnary hUnary hostHTransport
  exact
    ⟨negativeUnary, hostUnary, transportUnary, eANegative, negativeTHost,
      hostHTransport, negativePkg, hostPkg, transportPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
