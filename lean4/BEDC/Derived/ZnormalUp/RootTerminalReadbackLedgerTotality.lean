import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_terminal_readback_ledger_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal terminalRead →
        Cont terminalRead transports readback →
          PkgSig bundle readback pkg →
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row terminal ∨ hsame row normal ∨ hsame row terminalRead ∨
                    hsame row transports ∨ hsame row readback)
                (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                hsame ∧
              UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
                UnaryHistory normal ∧ UnaryHistory terminalRead ∧ UnaryHistory transports ∧
                  UnaryHistory readback ∧ Cont typed fuel terminal ∧
                    Cont terminal normal terminalRead ∧
                      Cont terminalRead transports readback ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalRead terminalReadTransportsReadback readbackPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalReadUnary transportsUnary terminalReadTransportsReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row normal ∨ hsame row terminalRead ∨
              hsame row transports ∨ hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro readback ⟨hsame_refl readback, readbackUnary⟩
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
        exact ⟨source.left, readbackPkg⟩
    }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, terminalReadUnary,
      transportsUnary, readbackUnary, typedFuelTerminal, terminalNormalRead,
      terminalReadTransportsReadback, provenancePkg, readbackPkg⟩

end BEDC.Derived.ZnormalUp
