import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_readback_display [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal hostRead →
          PkgSig bundle hostRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                    hsame row hostRead)
                (fun row : BHist => hsame row hostRead ∧ PkgSig bundle hostRead pkg)
                hsame ∧
              hsame terminalRead terminal ∧ UnaryHistory typed ∧ UnaryHistory fuel ∧
                UnaryHistory terminal ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
                  UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                    UnaryHistory name ∧ UnaryHistory hostRead ∧ Cont typed fuel terminalRead ∧
                      Cont terminalRead normal hostRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalHostRead hostReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have terminalReadTerminal : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalHostRead
  have sourceHost :
      (fun row : BHist => hsame row hostRead ∧ UnaryHistory row) hostRead := by
    exact ⟨hsame_refl hostRead, hostReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨ hsame row hostRead)
          (fun row : BHist => hsame row hostRead ∧ PkgSig bundle hostRead pkg)
          hsame := {
      core := {
        carrier_inhabited := Exists.intro hostRead sourceHost
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro row source
        exact ⟨source.left, hostReadPkg⟩
    }
  exact
    ⟨cert, terminalReadTerminal, typedUnary, fuelUnary, terminalUnary, normalUnary,
      continuationUnary, transportsUnary, routesUnary, provenanceUnary, nameUnary,
      hostReadUnary, typedFuelTerminalRead, terminalReadNormalHostRead, provenancePkg,
      namePkg, hostReadPkg⟩

end BEDC.Derived.ZnormalUp
