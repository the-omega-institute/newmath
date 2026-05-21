import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_namecert_readiness_surface [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      namecertRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal terminalRead →
        Cont terminalRead name namecertRead →
          PkgSig bundle namecertRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namecertRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row terminal ∨ hsame row normal ∨ hsame row terminalRead ∨
                    hsame row name ∨ hsame row namecertRead)
                (fun row : BHist => hsame row namecertRead ∧ PkgSig bundle namecertRead pkg)
                hsame ∧
              UnaryHistory terminalRead ∧ UnaryHistory namecertRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet terminalNormalRead terminalReadNameCertRead namecertReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRead
  have namecertReadUnary : UnaryHistory namecertRead :=
    unary_cont_closed terminalReadUnary nameUnary terminalReadNameCertRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namecertRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row normal ∨ hsame row terminalRead ∨
              hsame row name ∨ hsame row namecertRead)
          (fun row : BHist => hsame row namecertRead ∧ PkgSig bundle namecertRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namecertRead ⟨hsame_refl namecertRead, namecertReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namecertReadPkg⟩
  }
  exact ⟨cert, terminalReadUnary, namecertReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
