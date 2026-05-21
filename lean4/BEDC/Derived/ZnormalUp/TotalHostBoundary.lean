import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal hostRead →
        PkgSig bundle hostRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row hostRead)
              (fun row : BHist => hsame row hostRead ∧ PkgSig bundle hostRead pkg)
              hsame ∧
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory hostRead ∧ Cont typed fuel terminal ∧
                Cont terminal normal hostRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalHostRead hostReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalHostRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row hostRead)
          (fun row : BHist => hsame row hostRead ∧ PkgSig bundle hostRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro hostRead ⟨hsame_refl hostRead, hostReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
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
        exact ⟨source.left, hostReadPkg⟩
    }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, hostReadUnary,
      typedFuelTerminal, terminalNormalHostRead, provenancePkg, hostReadPkg⟩

end BEDC.Derived.ZnormalUp
