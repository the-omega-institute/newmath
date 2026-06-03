import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceLocatedWindowChoice [AskSetup] [PackageSetup]
    {S W Q R I H C P N windowRead readbackRead sealRead boundRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg →
      Cont S W windowRead →
        Cont windowRead Q readbackRead →
          Cont readbackRead R sealRead →
            Cont sealRead I boundRead →
              Cont boundRead H locatedRead →
                PkgSig bundle boundRead pkg →
                  UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                      UnaryHistory locatedRead ∧ Cont S W windowRead ∧
                        Cont windowRead Q readbackRead ∧ Cont readbackRead R sealRead ∧
                          Cont sealRead I boundRead ∧ Cont boundRead H locatedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier windowRoute readbackRoute sealRoute boundRoute locatedRoute boundPkg
  obtain ⟨SUnary, WUnary, QUnary, RUnary, IUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _intervalRoute, _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed SUnary WUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary QUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary RUnary sealRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sealUnary IUnary boundRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed boundUnary HUnary locatedRoute
  exact
    ⟨windowUnary, readbackUnary, sealUnary, boundUnary, locatedUnary, windowRoute,
      readbackRoute, sealRoute, boundRoute, locatedRoute, provenancePkg, boundPkg⟩

end BEDC.Derived.BoundedRealSequenceUp
