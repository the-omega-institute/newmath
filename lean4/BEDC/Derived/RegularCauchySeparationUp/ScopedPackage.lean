import BEDC.Derived.RegularCauchySeparationUp.ObligationScope
import BEDC.Derived.RegularCauchySeparationUp.RealSealScope

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RegularCauchySeparationCarrier_public_interface [AskSetup] [PackageSetup]
    {L R W D M E H C P N leftWindow rightWindow toleranceRead modulusRead sealRead zeroSeal
      supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory M →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont L W leftWindow →
                          Cont R W rightWindow →
                            hsame leftWindow rightWindow →
                              Cont leftWindow D toleranceRead →
                                Cont toleranceRead M modulusRead →
                                  Cont modulusRead E sealRead →
                                    Cont modulusRead E zeroSeal →
                                      Cont sealRead H supportRead →
                                        PkgSig bundle sealRead pkg →
                                          PkgSig bundle zeroSeal pkg →
                                            PkgSig bundle P pkg →
                                              PkgSig bundle N pkg →
                                                PkgSig bundle supportRead pkg →
                                                  SemanticNameCert
                                                      (fun row : BHist =>
                                                        hsame row supportRead ∧
                                                          UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row L ∨ hsame row R ∨
                                                          hsame row W ∨ hsame row D ∨
                                                            hsame row M ∨ hsame row E ∨
                                                              hsame row H ∨ hsame row C ∨
                                                                hsame row P ∨ hsame row N ∨
                                                                  hsame row sealRead ∨
                                                                    hsame row supportRead)
                                                      (fun row : BHist =>
                                                        UnaryHistory row ∧
                                                          Cont modulusRead E sealRead ∧
                                                            Cont sealRead H supportRead ∧
                                                              PkgSig bundle P pkg ∧
                                                                PkgSig bundle N pkg)
                                                      hsame ∧
                                                    regularCauchySeparationFromEventFlow
                                                        (regularCauchySeparationToEventFlow
                                                          (RegularCauchySeparationUp.mk
                                                            L R W D M E H C P N)) =
                                                      some
                                                        (RegularCauchySeparationUp.mk
                                                          L R W D M E H C P N) ∧
                                                      UnaryHistory sealRead ∧
                                                        UnaryHistory supportRead ∧
                                                          PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary supportUnary
    transportUnary provenanceUnary nameUnary leftRoute rightRoute sameWindow toleranceRoute
    modulusRoute sealRoute zeroRoute supportRoute sealPkg zeroPkg provenancePkg namePkg
    supportPkg
  have realSealScope :=
    RegularCauchySeparationCarrier_real_seal_scope
      (L := L) (R := R) (W := W) (D := D) (M := M) (E := E) (H := H) (C := C)
      (P := P) (N := N) (leftWindow := leftWindow) (rightWindow := rightWindow)
      (toleranceRead := toleranceRead) (modulusRead := modulusRead)
      (sealRead := sealRead) (supportRead := supportRead) (bundle := bundle) (pkg := pkg)
      leftUnary rightUnary windowUnary dyadicUnary modulusUnary sealUnary supportUnary
      transportUnary provenanceUnary nameUnary leftRoute rightRoute toleranceRoute modulusRoute
      sealRoute supportRoute provenancePkg namePkg supportPkg
  obtain ⟨cert, _leftWindowUnary, _rightWindowUnary, _toleranceUnary, _modulusReadUnary,
    sealReadUnary, supportReadUnary⟩ := realSealScope
  have scopedPackage :=
    RegularCauchySeparationCarrier_scoped_package
      (L := L) (R := R) (W := W) (D := D) (M := M) (E := E) (H := H) (C := C)
      (P := P) (N := N) (leftWindow := leftWindow) (rightWindow := rightWindow)
      (toleranceRead := toleranceRead) (modulusRead := modulusRead)
      (sealRead := sealRead) (zeroSeal := zeroSeal) (supportRead := supportRead)
      (bundle := bundle) (pkg := pkg) leftUnary rightUnary windowUnary dyadicUnary
      modulusUnary sealUnary supportUnary transportUnary provenanceUnary nameUnary leftRoute
      rightRoute sameWindow toleranceRoute modulusRoute sealRoute zeroRoute supportRoute
      sealPkg zeroPkg provenancePkg namePkg supportPkg
  obtain ⟨roundTrip, _sealReadUnary, _zeroSealUnary, _supportReadUnary, _zeroEndpoint,
    supportPkgOut⟩ := scopedPackage
  exact ⟨cert, roundTrip, sealReadUnary, supportReadUnary, supportPkgOut⟩

end BEDC.Derived.RegularCauchySeparationUp
