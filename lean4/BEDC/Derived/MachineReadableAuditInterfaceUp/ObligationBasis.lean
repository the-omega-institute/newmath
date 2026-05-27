import BEDC.Derived.MachineReadableAuditInterfaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MachineReadableAuditInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MachineReadableAuditInterfaceCarrier [AskSetup] [PackageSetup]
    (S C E R F H K P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
    UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S C E ∧ Cont R F H ∧ Cont H K P ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MachineReadableAuditInterface_obligation_basis [AskSetup] [PackageSetup]
    {S C E R F H K P N schemaRead reportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont S C schemaRead ->
        Cont E R reportRead ->
          Cont reportRead K replayRead ->
            PkgSig bundle replayRead pkg ->
              UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
                UnaryHistory F ∧ UnaryHistory K ∧ UnaryHistory N ∧
                  UnaryHistory schemaRead ∧ UnaryHistory reportRead ∧
                    UnaryHistory replayRead ∧ Cont S C schemaRead ∧
                      Cont E R reportRead ∧ Cont reportRead K replayRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier schemaRoute reportRoute replayRoute replayPkg
  obtain ⟨SUnary, CUnary, EUnary, RUnary, FUnary, _HUnary, KUnary, _PUnary,
    NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, namePkg⟩ := carrier
  have schemaUnary : UnaryHistory schemaRead :=
    unary_cont_closed SUnary CUnary schemaRoute
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed EUnary RUnary reportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed reportUnary KUnary replayRoute
  exact
    ⟨SUnary, CUnary, EUnary, RUnary, FUnary, KUnary, NUnary, schemaUnary,
      reportUnary, replayUnary, schemaRoute, reportRoute, replayRoute, carrierPkg,
      namePkg, replayPkg⟩

end BEDC.Derived.MachineReadableAuditInterfaceUp
