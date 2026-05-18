import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalFuelReadbackTasteGateRoute [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name fuelRead
      tasteGateRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel fuelRead →
        Cont fuelRead continuation tasteGateRow →
          PkgSig bundle tasteGateRow pkg →
            SemanticNameCert
                (fun row : BHist => hsame row tasteGateRow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row fuelRead ∨
                    hsame row tasteGateRow)
                (fun row : BHist => PkgSig bundle tasteGateRow pkg ∧ hsame row tasteGateRow)
                hsame ∧
              hsame fuelRead terminal ∧ UnaryHistory fuelRead ∧
                UnaryHistory tasteGateRow ∧ Cont terminal normal continuation ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle tasteGateRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelFuelRead fuelReadContinuationTasteGate tasteGatePkg
  have packetWitness := packet
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  obtain ⟨fuelReadSame, fuelReadUnary, terminalNormalContinuation, provenancePkg⟩ :=
    ZnormalPacket_root_terminal_normality_determinacy packetWitness typedFuelFuelRead
  have tasteGateUnary : UnaryHistory tasteGateRow :=
    unary_cont_closed fuelReadUnary continuationUnary fuelReadContinuationTasteGate
  have tasteGateSource :
      (fun row : BHist => hsame row tasteGateRow ∧ UnaryHistory row) tasteGateRow := by
    exact ⟨hsame_refl tasteGateRow, tasteGateUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tasteGateRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row fuelRead ∨ hsame row tasteGateRow)
          (fun row : BHist => PkgSig bundle tasteGateRow pkg ∧ hsame row tasteGateRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tasteGateRow tasteGateSource
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨tasteGatePkg, source.left⟩
  }
  exact
    ⟨cert, fuelReadSame, fuelReadUnary, tasteGateUnary, terminalNormalContinuation,
      provenancePkg, tasteGatePkg⟩

end BEDC.Derived.ZnormalUp
