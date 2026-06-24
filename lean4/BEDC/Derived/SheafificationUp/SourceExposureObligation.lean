import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSourceExposureObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        PkgSig bundle sourceRead pkg →
          UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J ∧ UnaryHistory P ∧
            UnaryHistory L ∧ UnaryHistory sourceRead ∧ Cont C T sourceRead ∧
              PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute sourcePkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, LUnary, _GUnary, _SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, qPkg, namePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed CUnary TUnary sourceRoute
  exact
    ⟨CUnary, TUnary, JUnary, PUnary, LUnary, sourceUnary, sourceRoute, qPkg, namePkg,
      sourcePkg⟩

end BEDC.Derived.SheafificationUp
