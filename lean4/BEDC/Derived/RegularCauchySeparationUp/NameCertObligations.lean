import BEDC.Derived.RegularCauchySeparationUp.ModulusBoundary
import BEDC.Derived.RegularCauchySeparationUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {L R W D M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
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
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row L ∨ hsame row R ∨ hsame row W ∨
                                      hsame row D ∨ hsame row M ∨ hsame row E ∨
                                        hsame row H ∨ hsame row C ∨ hsame row P ∨
                                          hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧
                                  UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory E ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro lUnary rUnary wUnary dUnary mUnary eUnary _hUnary _cUnary _pUnary nUnary pPkg
    nPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row M ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, nPkg⟩
  }
  exact
    ⟨cert, lUnary, rUnary, wUnary, dUnary, mUnary, eUnary, pPkg, nPkg⟩

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
