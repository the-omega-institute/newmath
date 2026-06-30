import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCoverSiteGluingLedger [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N siteGluing : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont J G siteGluing →
        PkgSig bundle siteGluing pkg →
          UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J ∧ UnaryHistory P ∧
            UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory siteGluing ∧
              Cont J G siteGluing ∧ PkgSig bundle siteGluing pkg := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier siteGluingRoute siteGluingPkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, lUnary, gUnary, _sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have siteGluingUnary : UnaryHistory siteGluing :=
    unary_cont_closed jUnary gUnary siteGluingRoute
  exact
    ⟨cUnary, tUnary, jUnary, pUnary, lUnary, gUnary, siteGluingUnary,
      siteGluingRoute, siteGluingPkg⟩

end BEDC.Derived.SheafificationUp
