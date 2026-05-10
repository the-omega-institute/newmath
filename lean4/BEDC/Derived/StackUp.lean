import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem StackDescent_obligation_surface [AskSetup] [PackageSetup]
    {site objectRows arrowRows descentLedger carrierRow : BHist}
    {schemeBundle sheafBundle : ProbeBundle ProbeName} {schemePkg sheafPkg : Pkg} :
    UnaryHistory site -> UnaryHistory objectRows -> UnaryHistory arrowRows ->
      Cont objectRows arrowRows descentLedger -> Cont site descentLedger carrierRow ->
        PkgSig schemeBundle site schemePkg -> PkgSig sheafBundle descentLedger sheafPkg ->
          UnaryHistory carrierRow ∧ hsame carrierRow (append site descentLedger) ∧
            Cont objectRows arrowRows descentLedger ∧ PkgSig sheafBundle descentLedger sheafPkg := by
  intro siteUnary objectRowsUnary arrowRowsUnary descentCont carrierCont _schemePkgSig sheafPkgSig
  have descentUnary : UnaryHistory descentLedger :=
    unary_cont_closed objectRowsUnary arrowRowsUnary descentCont
  have carrierUnary : UnaryHistory carrierRow :=
    unary_cont_closed siteUnary descentUnary carrierCont
  exact ⟨carrierUnary, carrierCont, descentCont, sheafPkgSig⟩

end BEDC.Derived.StackUp
