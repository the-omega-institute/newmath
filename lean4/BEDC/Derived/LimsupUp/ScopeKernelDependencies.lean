import BEDC.Derived.LimsupUp

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupScopeKernelDependencies [AskSetup] [PackageSetup]
    {S U D T H C P N upperRead lowerRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupCarrier S U D T H C P N bundle pkg ->
      Cont S U upperRead ->
        Cont upperRead D lowerRead ->
          Cont lowerRead T sealRead ->
            Cont sealRead H named ->
              PkgSig bundle named pkg ->
                UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory T ∧
                  UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory named ∧ Cont S U upperRead ∧
                        Cont upperRead D lowerRead ∧ Cont lowerRead T sealRead ∧
                          Cont sealRead H named ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg ∧ PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier upperRoute lowerRoute sealRoute namedRoute namedPackage
  obtain
    ⟨sUnary, uUnary, dUnary, tUnary, hUnary, cUnary, nUnary, _sourceUpperRoute,
      _cutRoute, provenancePackage, namePackage⟩ := carrier
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed sUnary uUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed upperUnary dUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary tUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary hUnary namedRoute
  exact
    ⟨sUnary, uUnary, dUnary, tUnary, hUnary, cUnary, nUnary, upperUnary, lowerUnary,
      sealUnary, namedUnary, upperRoute, lowerRoute, sealRoute, namedRoute,
      provenancePackage, namePackage, namedPackage⟩

end BEDC.Derived.LimsupUp
