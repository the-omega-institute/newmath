import BEDC.Derived.RegularCauchySeparationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_modulus_boundary [AskSetup] [PackageSetup]
    {L R W D M E H C P N leftWindow rightWindow toleranceRead modulusRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory M →
              UnaryHistory E →
                Cont L W leftWindow →
                  Cont R W rightWindow →
                    Cont leftWindow D toleranceRead →
                      Cont toleranceRead M modulusRead →
                        Cont modulusRead E sealRead →
                          PkgSig bundle sealRead pkg →
                            UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                              UnaryHistory toleranceRead ∧ UnaryHistory modulusRead ∧
                                UnaryHistory sealRead ∧ Cont L W leftWindow ∧
                                  Cont R W rightWindow ∧
                                    Cont leftWindow D toleranceRead ∧
                                      Cont toleranceRead M modulusRead ∧
                                        Cont modulusRead E sealRead ∧
                                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary leftRoute
    rightRoute toleranceRoute modulusRoute sealRoute sealPkg
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary windowUnary leftRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed rightUnary windowUnary rightRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed leftWindowUnary dyadicUnary toleranceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary modulusUnary modulusRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusReadUnary sealUnary sealRoute
  exact
    ⟨leftWindowUnary, rightWindowUnary, toleranceUnary, modulusReadUnary, sealReadUnary,
      leftRoute, rightRoute, toleranceRoute, modulusRoute, sealRoute, sealPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
