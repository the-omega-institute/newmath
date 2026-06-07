import BEDC.Derived.CauchyQuotientBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyQuotientBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyQuotientBoundaryCarrier [AskSetup] [PackageSetup]
    (S Q F D W R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory ProbeBundle Pkg PkgSig
  UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory F ∧ UnaryHistory D ∧
    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem CauchyQuotientBoundaryCarrier_refusal_factorization [AskSetup] [PackageSetup]
    {S Q F D W R E H C P N sourceRead refusalRead dyadicRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyQuotientBoundaryCarrier S Q F D W R E H C P N bundle pkg →
      Cont S W sourceRead →
        Cont sourceRead F refusalRead →
          Cont refusalRead D dyadicRead →
            Cont dyadicRead R readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory sourceRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory sealRead ∧ Cont S W sourceRead ∧
                        Cont sourceRead F refusalRead ∧ Cont refusalRead D dyadicRead ∧
                          Cont dyadicRead R readbackRead ∧
                            Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier sourceRoute refusalRoute dyadicRoute readbackRoute sealRoute sealPkg
  obtain ⟨sUnary, _qUnary, fUnary, dUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary wUnary sourceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sourceUnary fUnary refusalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed refusalUnary dUnary dyadicRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed dyadicUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact
    ⟨sourceUnary, refusalUnary, dyadicUnary, readbackUnary, sealUnary, sourceRoute,
      refusalRoute, dyadicRoute, readbackRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyQuotientBoundaryUp
