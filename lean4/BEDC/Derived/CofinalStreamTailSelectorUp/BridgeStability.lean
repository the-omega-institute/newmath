import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorCarrier_bridge_stability [AskSetup] [PackageSetup]
    {epsilon W R D sigma A H C P N bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory epsilon →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory D →
            UnaryHistory sigma →
              UnaryHistory A →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont epsilon W R →
                          Cont R D sigma →
                            Cont sigma A bridgeRead →
                              PkgSig bundle N pkg →
                                UnaryHistory bridgeRead ∧ Cont epsilon W R ∧
                                  Cont R D sigma ∧ Cont sigma A bridgeRead ∧
                                    PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro _epsilonUnary _wUnary _rUnary _dUnary sigmaUnary aUnary _hUnary _cUnary
    _pUnary _nUnary epsilonWindow routeDyadic routeBridge namePkg
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sigmaUnary aUnary routeBridge
  exact ⟨bridgeUnary, epsilonWindow, routeDyadic, routeBridge, namePkg⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
