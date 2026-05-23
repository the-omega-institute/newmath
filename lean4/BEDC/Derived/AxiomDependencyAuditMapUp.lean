import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyAuditMapCarrier [AskSetup] [PackageSetup]
    (K M W A L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory A ∧
    UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont K M L ∧ Cont L A H ∧ Cont H C P ∧
        PkgSig bundle N pkg

theorem AxiomDependencyAuditMap_mode_totality [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        PkgSig bundle modeRead pkg →
          UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory A ∧
            UnaryHistory modeRead ∧ Cont M W modeRead ∧ Cont K M L ∧
              PkgSig bundle N pkg ∧ PkgSig bundle modeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute modePkg
  obtain ⟨kUnary, mUnary, wUnary, aUnary, _lUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    namePkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  exact
    ⟨kUnary, mUnary, wUnary, aUnary, modeUnary, modeRoute, claimModeLedger, namePkg,
      modePkg⟩

end BEDC.Derived.AxiomDependencyAuditMapUp
