import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.CauchyTailModulusFusionUp.TasteGate

namespace BEDC.Derived.CauchyTailModulusFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailModulusFusionCarrier [AskSetup] [PackageSetup]
    (t0 t1 mu0 mu1 tau v w0 w1 d0 d1 q0 q1 e h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory t0 ∧ UnaryHistory t1 ∧ UnaryHistory mu0 ∧ UnaryHistory mu1 ∧
    UnaryHistory tau ∧ UnaryHistory v ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
      UnaryHistory d0 ∧ UnaryHistory d1 ∧ UnaryHistory q0 ∧ UnaryHistory q1 ∧
        UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
          UnaryHistory n ∧ Cont t0 t1 tau ∧ Cont mu0 mu1 v ∧ Cont tau v w0 ∧
            Cont w0 w1 d0 ∧ Cont d0 d1 q0 ∧ Cont q0 q1 e ∧
              PkgSig bundle p pkg

theorem CauchyTailModulusFusionCarrier_shared_tail_exhaustion [AskSetup] [PackageSetup]
    {t0 t1 mu0 mu1 tau v w0 w1 d0 d1 q0 q1 e h c p n sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailModulusFusionCarrier t0 t1 mu0 mu1 tau v w0 w1 d0 d1 q0 q1 e h c p
        n bundle pkg ->
      Cont q0 q1 sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory t0 ∧ UnaryHistory t1 ∧ UnaryHistory mu0 ∧ UnaryHistory mu1 ∧
            UnaryHistory tau ∧ UnaryHistory v ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
              UnaryHistory d0 ∧ UnaryHistory d1 ∧ UnaryHistory q0 ∧ UnaryHistory q1 ∧
                UnaryHistory e ∧ UnaryHistory sealRead ∧ Cont t0 t1 tau ∧
                  Cont mu0 mu1 v ∧ Cont tau v w0 ∧ Cont w0 w1 d0 ∧
                    Cont d0 d1 q0 ∧ Cont q0 q1 sealRead ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier q0q1SealRead sealReadPkg
  obtain ⟨t0Unary, t1Unary, mu0Unary, mu1Unary, tauUnary, vUnary, w0Unary,
    w1Unary, d0Unary, d1Unary, q0Unary, q1Unary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, t0t1Tau, mu0mu1V, tauVW0, w0w1D0, d0d1Q0, _q0q1E, pPkg⟩ :=
      carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed q0Unary q1Unary q0q1SealRead
  exact
    ⟨t0Unary, t1Unary, mu0Unary, mu1Unary, tauUnary, vUnary, w0Unary, w1Unary,
      d0Unary, d1Unary, q0Unary, q1Unary, eUnary, sealReadUnary, t0t1Tau, mu0mu1V,
      tauVW0, w0w1D0, d0d1Q0, q0q1SealRead, pPkg, sealReadPkg⟩

end BEDC.Derived.CauchyTailModulusFusionUp
