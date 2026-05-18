import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootUnblockLedgerNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont gap name ledgerRead ->
      UnaryHistory gap ->
        UnaryHistory name ->
          PkgSig bundle provenance pkg ->
            authorizedGeneratorRecursorFromEventFlow
                (authorizedGeneratorRecursorToEventFlow
                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
                    audit transport routes provenance gap name)) =
              some
                (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
                  audit transport routes provenance gap name) ∧
              UnaryHistory ledgerRead ∧ Cont gap name ledgerRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro gapNameLedger gapUnary nameUnary provenancePkg
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed gapUnary nameUnary gapNameLedger
  exact ⟨roundTrip, ledgerUnary, gapNameLedger, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
