import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSitePlusBoundaryObligations [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sitePlus : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T J →
        Cont J P L →
          Cont L G S →
            Cont H R Q →
              hsame Q N →
                Cont C L sitePlus →
                  UnaryHistory sitePlus := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _siteRoute _restrictionRoute _gluingRoute _replayRoute _sameName sitePlusRoute
  obtain ⟨cUnary, _tUnary, _jUnary, _pUnary, lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  exact unary_cont_closed cUnary lUnary sitePlusRoute

end BEDC.Derived.SheafificationUp
