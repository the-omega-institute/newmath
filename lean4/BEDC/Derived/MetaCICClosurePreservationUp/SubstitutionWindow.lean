import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosurePreservationCarrier_substitution_window [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N window : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      UnaryHistory A →
        UnaryHistory C →
          UnaryHistory B →
      Cont A C G →
        Cont G B F →
          Cont C A window →
            PkgSig bundle P pkg →
              UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory G ∧ UnaryHistory B ∧
                UnaryHistory F ∧ UnaryHistory window ∧ Cont A C G ∧ Cont G B F ∧
                  Cont C A window ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier aUnary cUnary bUnary routeACG routeGBF routeCAWindow pPkg
  obtain ⟨_sourceS, _routeSAQ, _routeUBF, _routeCGR, _carrierPPkg, _nPkg⟩ := carrier
  have gUnary : UnaryHistory G := by
    exact unary_cont_closed aUnary cUnary routeACG
  have fUnary : UnaryHistory F := by
    exact unary_cont_closed gUnary bUnary routeGBF
  have windowUnary : UnaryHistory window := by
    exact unary_cont_closed cUnary aUnary routeCAWindow
  exact
    ⟨aUnary, cUnary, gUnary, bUnary, fUnary, windowUnary, routeACG, routeGBF,
      routeCAWindow, pPkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp
