import BEDC.Derived.LogicContradictionMetaLoopUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LogicContradictionMetaLoopUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LogicContradictionMetaLoopNonescapeCarrier [AskSetup] [PackageSetup]
    (P R M A T C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory P ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory A ∧
    UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory G ∧ UnaryHistory N ∧
      Cont P R M ∧ Cont M A C ∧ Cont T C G ∧ PkgSig bundle N pkg

theorem LogicContradictionMetaLoopCarrier_nonescape [AskSetup] [PackageSetup]
    {P R M A T C G N routeRead gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LogicContradictionMetaLoopNonescapeCarrier P R M A T C G N bundle pkg →
      Cont P R routeRead →
        Cont routeRead M gateRead →
          PkgSig bundle gateRead pkg →
            UnaryHistory P ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory A ∧
              UnaryHistory routeRead ∧ UnaryHistory gateRead ∧ Cont P R routeRead ∧
                Cont routeRead M gateRead ∧ Cont M A C ∧ Cont T C G ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle gateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier routeCont gateCont gatePkg
  obtain ⟨pUnary, rUnary, mUnary, aUnary, _tUnary, _cUnary, _gUnary, _nUnary,
    _carrierRoute, metaAudit, transportGate, localPkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed pUnary rUnary routeCont
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed routeUnary mUnary gateCont
  exact
    ⟨pUnary, rUnary, mUnary, aUnary, routeUnary, gateUnary, routeCont, gateCont,
      metaAudit, transportGate, localPkg, gatePkg⟩

end BEDC.Derived.LogicContradictionMetaLoopUp
