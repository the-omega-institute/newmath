import BEDC.Derived.UpperSemicontinuousUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UpperSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpperSemicontinuousCarrier_lower_dual_boundary [AskSetup] [PackageSetup]
    {X F S W R O H C P N upperRead lowerGraph lowerWindow lowerRead lowerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory F →
        UnaryHistory S →
          UnaryHistory W →
            UnaryHistory R →
              UnaryHistory O →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        UnaryHistory lowerGraph →
                          UnaryHistory lowerWindow →
                            PkgSig bundle P pkg →
                              Cont F W upperRead →
                                Cont lowerGraph lowerWindow lowerRead →
                                  Cont lowerRead O lowerSeal →
                                    PkgSig bundle upperRead pkg →
                                      PkgSig bundle lowerSeal pkg →
                                        UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧
                                          UnaryHistory W ∧ UnaryHistory R ∧
                                            UnaryHistory O ∧ UnaryHistory upperRead ∧
                                              UnaryHistory lowerRead ∧
                                                UnaryHistory lowerSeal ∧
                                                  Cont F W upperRead ∧
                                                    Cont lowerGraph lowerWindow lowerRead ∧
                                                      Cont lowerRead O lowerSeal ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle upperRead pkg ∧
                                                            PkgSig bundle lowerSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro xUnary fUnary sUnary wUnary rUnary oUnary _hUnary _cUnary _pUnary _nUnary
    lowerGraphUnary lowerWindowUnary provenancePkg upperRoute lowerReadRoute lowerSealRoute
    upperPkg lowerSealPkg
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed fUnary wUnary upperRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerGraphUnary lowerWindowUnary lowerReadRoute
  have lowerSealUnary : UnaryHistory lowerSeal :=
    unary_cont_closed lowerReadUnary oUnary lowerSealRoute
  exact
    ⟨xUnary, fUnary, sUnary, wUnary, rUnary, oUnary, upperReadUnary, lowerReadUnary,
      lowerSealUnary, upperRoute, lowerReadRoute, lowerSealRoute, provenancePkg, upperPkg,
      lowerSealPkg⟩

end BEDC.Derived.UpperSemicontinuousUp
