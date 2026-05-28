import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_unary_carry_entry [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name carryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation carryRead →
        PkgSig bundle carryRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row carryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
                  hsame row carryRead)
              (fun row : BHist =>
                hsame row carryRead ∧ PkgSig bundle carryRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory carryRead ∧ UnaryHistory normal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationCarry carryReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have carryReadUnary : UnaryHistory carryRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationCarry
  have sourceCarry :
      (fun row : BHist => hsame row carryRead ∧ UnaryHistory row) carryRead := by
    exact ⟨hsame_refl carryRead, carryReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row carryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row carryRead)
          (fun row : BHist =>
            hsame row carryRead ∧ PkgSig bundle carryRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro carryRead sourceCarry
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, carryReadPkg, provenancePkg⟩
  }
  exact ⟨cert, carryReadUnary, normalUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
