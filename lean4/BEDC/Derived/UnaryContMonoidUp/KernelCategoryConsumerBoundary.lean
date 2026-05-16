import BEDC.Derived.UnaryContMonoidUp

namespace BEDC.Derived.UnaryContMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UnaryContMonoidCarrier_kernel_category_consumer_boundary [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont ledger unitRight kernelRead ->
        PkgSig bundle kernelRead pkg ->
          UnaryHistory ledger /\ UnaryHistory unitRight /\ UnaryHistory kernelRead /\
            Cont ab name ledger /\ Cont a BHist.Empty unitRight /\
              Cont ledger unitRight kernelRead /\ hsame e BHist.Empty /\
                PkgSig bundle kernelRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier kernelRoute kernelPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, _leftUnitRoute, rightUnitRoute,
    ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryRightUnit : UnaryHistory unitRight :=
    unary_cont_closed unaryA unary_empty rightUnitRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have unaryKernelRead : UnaryHistory kernelRead :=
    unary_cont_closed unaryLedger unaryRightUnit kernelRoute
  exact
    ⟨unaryLedger, unaryRightUnit, unaryKernelRead, ledgerRoute, rightUnitRoute,
      kernelRoute, sameUnit, kernelPkg⟩

end BEDC.Derived.UnaryContMonoidUp
