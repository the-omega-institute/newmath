import BEDC.Derived.RegularCauchySeparationUp.ModulusBoundary

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_namecert_obligations [AskSetup] [PackageSetup]
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
                            regularCauchySeparationFromEventFlow
                                (regularCauchySeparationToEventFlow
                                  (RegularCauchySeparationUp.mk L R W D M E H C P N)) =
                              some (RegularCauchySeparationUp.mk L R W D M E H C P N) ∧
                              UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                                UnaryHistory toleranceRead ∧ UnaryHistory modulusRead ∧
                                  UnaryHistory sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary leftRoute
    rightRoute toleranceRoute modulusRoute sealRoute sealPkg
  have roundTrip :
      regularCauchySeparationFromEventFlow
          (regularCauchySeparationToEventFlow
            (RegularCauchySeparationUp.mk L R W D M E H C P N)) =
        some (RegularCauchySeparationUp.mk L R W D M E H C P N) :=
    RegularCauchySeparationTasteGate_single_carrier_alignment.right.left
      (RegularCauchySeparationUp.mk L R W D M E H C P N)
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
    ⟨roundTrip, leftWindowUnary, rightWindowUnary, toleranceUnary, modulusReadUnary,
      sealReadUnary, sealPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
