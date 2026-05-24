import BEDC.Derived.AuditMapFamilyUp.TasteGate

namespace BEDC.Derived.AuditMapFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapFamilyCarrier_strict_local_obstruction [AskSetup] [PackageSetup]
    {family inventory obstruction route frontier transport continuation provenance localName
      obstructionRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFamilyCarrier family inventory obstruction route frontier transport continuation
        provenance localName bundle pkg ->
      Cont obstruction continuation obstructionRead ->
        Cont obstructionRead localName terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory obstruction ∧ UnaryHistory continuation ∧
              UnaryHistory obstructionRead ∧ UnaryHistory terminalRead ∧
                Cont obstruction continuation obstructionRead ∧
                  Cont obstructionRead localName terminalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier obstructionContinuation obstructionReadLocal terminalPkg
  rcases carrier with
    ⟨_familyUnary, _inventoryUnary, obstructionUnary, _routeUnary, _frontierUnary,
      _transportUnary, continuationUnary, _provenanceUnary, localNameUnary,
      _familyInventoryTransport, _obstructionRouteContinuation, provenancePkg⟩
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary continuationUnary obstructionContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed obstructionReadUnary localNameUnary obstructionReadLocal
  exact
    ⟨obstructionUnary, continuationUnary, obstructionReadUnary, terminalReadUnary,
      obstructionContinuation, obstructionReadLocal, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuditMapFamilyUp
