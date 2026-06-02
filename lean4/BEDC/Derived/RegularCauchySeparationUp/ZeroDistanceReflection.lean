import BEDC.Derived.RegularCauchySeparationUp.ModulusBoundary

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_zero_distance_reflection [AskSetup] [PackageSetup]
    {L R W D M E H C P N leftWindow rightWindow toleranceRead modulusRead zeroSeal :
      BHist}
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
                          Cont modulusRead E zeroSeal ->
                            PkgSig bundle zeroSeal pkg ->
                              UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                                UnaryHistory toleranceRead ∧ UnaryHistory modulusRead ∧
                                  UnaryHistory zeroSeal ∧ hsame leftWindow rightWindow ∧
                                    hsame zeroSeal (append modulusRead E) ∧
                                      PkgSig bundle zeroSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary leftRoute
    rightRoute sameWindow toleranceRoute modulusRoute sealRoute sealPkg
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary windowUnary leftRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed rightUnary windowUnary rightRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed leftWindowUnary dyadicUnary toleranceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary modulusUnary modulusRoute
  have zeroSealUnary : UnaryHistory zeroSeal :=
    unary_cont_closed modulusReadUnary sealUnary sealRoute
  have zeroEndpoint : hsame zeroSeal (append modulusRead E) := sealRoute
  exact
    ⟨leftWindowUnary, rightWindowUnary, toleranceUnary, modulusReadUnary, zeroSealUnary,
      sameWindow, zeroEndpoint, sealPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
