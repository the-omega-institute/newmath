import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootNameCertComponentExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name componentRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont routes name componentRead →
        PkgSig bundle componentRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row componentRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row terminal ∨ hsame row normal ∨
                  hsame row continuation ∨ hsame row componentRead)
              (fun row : BHist => hsame row componentRead ∧ PkgSig bundle componentRead pkg)
              hsame ∧
            UnaryHistory componentRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle componentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet routesNameComponentRead componentReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have componentReadUnary : UnaryHistory componentRead :=
    unary_cont_closed routesUnary nameUnary routesNameComponentRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row componentRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row componentRead)
          (fun row : BHist => hsame row componentRead ∧ PkgSig bundle componentRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro componentRead ⟨hsame_refl componentRead, componentReadUnary⟩
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
        exact ⟨source.left, componentReadPkg⟩
    }
  exact ⟨cert, componentReadUnary, provenancePkg, componentReadPkg⟩

end BEDC.Derived.ZnormalUp
