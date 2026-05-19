import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_refusal_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute consumer normalRead normalwordRoute hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          Cont terminalRoute transports consumer →
            Cont normal continuation normalRead →
              Cont normalRead routes normalwordRoute →
                PkgSig bundle consumer pkg →
                  PkgSig bundle normalwordRoute pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                            hsame row terminalRoute ∨ hsame row consumer)
                        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                        hsame ∧
                      hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                        UnaryHistory normalRead ∧ UnaryHistory normalwordRoute ∧
                          Cont normal continuation normalRead ∧
                            Cont normalRead routes normalwordRoute ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle consumer pkg ∧
                                  PkgSig bundle normalwordRoute pkg ∧
                                    (Cont normalwordRoute (BHist.e0 hostTail) normalRead →
                                      False) ∧
                                      (Cont normalwordRoute (BHist.e1 hostTail) normalRead →
                                        False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute
    terminalRouteTransportsConsumer normalContinuationNormalRead normalReadRoutesNormalword
    consumerPkg normalwordRoutePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalTerminalRoute
      terminalNormalContinuation
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalRouteUnary transportsUnary terminalRouteTransportsConsumer
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalRead
  have normalwordRouteUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesNormalword
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row terminalRoute ∨ hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  have e0Refusal : Cont normalwordRoute (BHist.e0 hostTail) normalRead → False :=
    fun back =>
      cont_mutual_extension_right_tail_absurd.left normalReadRoutesNormalword back
  have e1Refusal : Cont normalwordRoute (BHist.e1 hostTail) normalRead → False :=
    fun back =>
      cont_mutual_extension_right_tail_absurd.right normalReadRoutesNormalword back
  exact
    ⟨cert, terminalReadSame, terminalRouteSame, normalReadUnary, normalwordRouteUnary,
      normalContinuationNormalRead, normalReadRoutesNormalword, namePkg, provenancePkg,
      consumerPkg, normalwordRoutePkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZnormalUp
