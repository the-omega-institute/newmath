import BEDC.Derived.RegularCauchySeparationUp.ZeroDistanceReflection

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_obligation_scope [AskSetup] [PackageSetup]
    {L R W D M E _H _C _P _N leftWindow rightWindow toleranceRead modulusRead sealRead
      zeroSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory M ->
              UnaryHistory E ->
                Cont L W leftWindow ->
                  Cont R W rightWindow ->
                    hsame leftWindow rightWindow ->
                      Cont leftWindow D toleranceRead ->
                        Cont toleranceRead M modulusRead ->
                          Cont modulusRead E sealRead ->
                            Cont modulusRead E zeroSeal ->
                              PkgSig bundle sealRead pkg ->
                                PkgSig bundle zeroSeal pkg ->
                                  UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                                    UnaryHistory toleranceRead ∧ UnaryHistory modulusRead ∧
                                      UnaryHistory sealRead ∧ UnaryHistory zeroSeal ∧
                                        Cont L W leftWindow ∧ Cont R W rightWindow ∧
                                          Cont leftWindow D toleranceRead ∧
                                            Cont toleranceRead M modulusRead ∧
                                              Cont modulusRead E sealRead ∧
                                                Cont modulusRead E zeroSeal ∧
                                                  hsame leftWindow rightWindow ∧
                                                    hsame zeroSeal (append modulusRead E) ∧
                                                      PkgSig bundle sealRead pkg ∧
                                                        PkgSig bundle zeroSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary leftRoute
    rightRoute sameWindow toleranceRoute modulusRoute sealRoute zeroRoute sealPkg zeroPkg
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
  have zeroSealUnary : UnaryHistory zeroSeal :=
    unary_cont_closed modulusReadUnary sealUnary zeroRoute
  have zeroEndpoint : hsame zeroSeal (append modulusRead E) := zeroRoute
  exact
    ⟨leftWindowUnary, rightWindowUnary, toleranceUnary, modulusReadUnary, sealReadUnary,
      zeroSealUnary, leftRoute, rightRoute, toleranceRoute, modulusRoute, sealRoute,
      zeroRoute, sameWindow, zeroEndpoint, sealPkg, zeroPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
