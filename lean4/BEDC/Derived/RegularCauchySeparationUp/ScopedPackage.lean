import BEDC.Derived.RegularCauchySeparationUp.ObligationScope

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_scoped_package [AskSetup] [PackageSetup]
    {L R W D M E H C P N leftWindow rightWindow toleranceRead modulusRead sealRead zeroSeal
      supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory M ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont L W leftWindow ->
                          Cont R W rightWindow ->
                            hsame leftWindow rightWindow ->
                              Cont leftWindow D toleranceRead ->
                                Cont toleranceRead M modulusRead ->
                                  Cont modulusRead E sealRead ->
                                    Cont modulusRead E zeroSeal ->
                                      Cont sealRead H supportRead ->
                                        PkgSig bundle sealRead pkg ->
                                          PkgSig bundle zeroSeal pkg ->
                                            PkgSig bundle P pkg ->
                                              PkgSig bundle N pkg ->
                                                PkgSig bundle supportRead pkg ->
                                                  regularCauchySeparationFromEventFlow
                                                      (regularCauchySeparationToEventFlow
                                                        (RegularCauchySeparationUp.mk
                                                          L R W D M E H C P N)) =
                                                    some
                                                      (RegularCauchySeparationUp.mk
                                                        L R W D M E H C P N) ∧
                                                    UnaryHistory sealRead ∧
                                                      UnaryHistory zeroSeal ∧
                                                        UnaryHistory supportRead ∧
                                                          hsame zeroSeal
                                                            (append modulusRead E) ∧
                                                            PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary supportUnary
    _transportUnary _provenanceUnary _nameUnary leftRoute _rightRoute _sameWindow
    toleranceRoute modulusRoute sealRoute zeroRoute supportRoute _sealPkg _zeroPkg _provenancePkg
    _namePkg supportPkg
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary windowUnary leftRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed leftWindowUnary dyadicUnary toleranceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary modulusUnary modulusRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusReadUnary sealUnary sealRoute
  have zeroSealUnary : UnaryHistory zeroSeal :=
    unary_cont_closed modulusReadUnary sealUnary zeroRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed sealReadUnary supportUnary supportRoute
  have roundTrip :
      regularCauchySeparationFromEventFlow
          (regularCauchySeparationToEventFlow
            (RegularCauchySeparationUp.mk L R W D M E H C P N)) =
        some (RegularCauchySeparationUp.mk L R W D M E H C P N) :=
    RegularCauchySeparationTasteGate_single_carrier_alignment.right.left
      (RegularCauchySeparationUp.mk L R W D M E H C P N)
  have zeroEndpoint : hsame zeroSeal (append modulusRead E) := zeroRoute
  exact ⟨roundTrip, sealReadUnary, zeroSealUnary, supportReadUnary, zeroEndpoint, supportPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
