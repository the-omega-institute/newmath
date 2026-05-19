import BEDC.Derived.CauchyWindowTransducerUp.NameCertObligations

namespace BEDC.Derived.CauchyWindowTransducerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyWindowTransducerUp_StdBridge [AskSetup] [PackageSetup]
    {S D W R E L H C P N sealRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    CauchyWindowTransducerCarrier S D W R E L H C P N →
      Cont E L sealRead →
        PkgSig bundle sealRead pkg →
          UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧
            UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory sealRead ∧ Cont S D W ∧
              Cont W R E ∧ Cont E L sealRead ∧ hsame N E ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier contELSeal pkgSeal
  obtain ⟨unaryS, unaryD, unaryW, unaryR, unaryE, unaryL, _unaryH, _unaryC,
    _unaryP, _unaryN, contSDW, contWRE, sameNE⟩ := carrier
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryE unaryL contELSeal
  exact ⟨unaryS, unaryD, unaryW, unaryR, unaryE, unaryL, unarySeal, contSDW, contWRE,
    contELSeal, sameNE, pkgSeal⟩

end BEDC.Derived.CauchyWindowTransducerUp
