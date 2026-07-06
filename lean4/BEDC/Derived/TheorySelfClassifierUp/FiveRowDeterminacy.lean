import BEDC.Derived.TheorySelfClassifierUp.TasteGate

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_five_row_determinacy [AskSetup] [PackageSetup]
    {G E R P A L H C Q N G' E' R' P' A' L' H' C' Q' N' read read' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg →
      TheorySelfClassifierCarrier G' E' R' P' A' L' H' C' Q' N' bundle pkg →
        hsame G G' →
          hsame E E' →
            hsame R R' →
              hsame P P' →
                hsame A A' →
                  hsame L L' →
                    Cont A L read →
                      Cont A' L' read' →
                        hsame read read' ∧ UnaryHistory read ∧ UnaryHistory read' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier carrier' _sameG _sameE _sameR _sameP sameA sameL route route'
  obtain ⟨_gUnary, _eUnary, _rUnary, _pUnary, aUnary, lUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _generatorEqualityRoute, _recursorPurityRoute,
    _classifierRoute, _provenancePkg⟩ := carrier
  obtain ⟨_gUnary', _eUnary', _rUnary', _pUnary', aUnary', lUnary', _hUnary',
    _cUnary', _qUnary', _nUnary', _generatorEqualityRoute',
    _recursorPurityRoute', _classifierRoute', _provenancePkg'⟩ := carrier'
  have readUnary : UnaryHistory read :=
    unary_cont_closed aUnary lUnary route
  have readUnary' : UnaryHistory read' :=
    unary_cont_closed aUnary' lUnary' route'
  have sameRead : hsame read read' :=
    cont_respects_hsame sameA sameL route route'
  exact ⟨sameRead, readUnary, readUnary'⟩

end BEDC.Derived.TheorySelfClassifierUp
