import BEDC.Derived.RegularCauchyAbsUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {R E realRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory E →
        Cont R E realRead →
          PkgSig bundle R pkg →
            PkgSig bundle realRead pkg →
              UnaryHistory realRead ∧
                Cont R E realRead ∧
                  PkgSig bundle R pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro unaryR unaryE realRoute rPkg realPkg
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryR unaryE realRoute
  exact ⟨realUnary, realRoute, rPkg, realPkg⟩

end BEDC.Derived.RegularCauchyAbsUp
