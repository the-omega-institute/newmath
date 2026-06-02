import BEDC.Derived.RieszRepresentationUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationHilbertFunctionalBridge [AskSetup] [PackageSetup]
    {source functional representing ledger branch transportedFunctional transportedRepresenting
      transportedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory functional ->
        UnaryHistory representing ->
          UnaryHistory ledger ->
            Cont functional representing ledger ->
              Cont source functional transportedFunctional ->
                Cont transportedFunctional representing transportedRepresenting ->
                  Cont transportedRepresenting ledger transportedLedger ->
                    PkgSig bundle transportedLedger pkg ->
                      UnaryHistory transportedFunctional ∧ UnaryHistory transportedRepresenting ∧
                        UnaryHistory transportedLedger ∧ Cont functional representing ledger ∧
                          Cont source functional transportedFunctional ∧
                            Cont transportedFunctional representing transportedRepresenting ∧
                              Cont transportedRepresenting ledger transportedLedger ∧
                                PkgSig bundle transportedLedger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro sourceUnary functionalUnary representingUnary ledgerUnary functionalRepresenting
    sourceFunctional functionalRepresentingTransport representingLedgerTransport packageSeal
  have transportedFunctionalUnary : UnaryHistory transportedFunctional :=
    unary_cont_closed sourceUnary functionalUnary sourceFunctional
  have transportedRepresentingUnary : UnaryHistory transportedRepresenting :=
    unary_cont_closed transportedFunctionalUnary representingUnary functionalRepresentingTransport
  have transportedLedgerUnary : UnaryHistory transportedLedger :=
    unary_cont_closed transportedRepresentingUnary ledgerUnary representingLedgerTransport
  exact
    ⟨transportedFunctionalUnary, transportedRepresentingUnary, transportedLedgerUnary,
      functionalRepresenting, sourceFunctional, functionalRepresentingTransport,
      representingLedgerTransport, packageSeal⟩

end BEDC.Derived.RieszRepresentationUp
