import BEDC.Derived.DiniUniformConvergenceUp.NameCertObligations

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiniUniformConvergenceCarrier_finite_net_monotone_tail_scope [AskSetup]
    [PackageSetup]
    {compact finiteNet family modulus windows readback sealRow transportRow replayRow provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier compact finiteNet family modulus windows readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont compact finiteNet family ->
        Cont family windows readback ->
          Cont readback sealRow modulus ->
            PkgSig bundle localName pkg ->
              PkgSig bundle modulus pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row windows ∨ hsame row readback ∨ hsame row sealRow ∨
                        hsame row modulus) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨
                        hsame row modulus ∨ hsame row windows ∨ hsame row readback ∨
                          hsame row sealRow ∨ hsame row localName)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle modulus pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory family ∧ UnaryHistory readback ∧ UnaryHistory modulus := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactFiniteNet familyWindows readbackSeal localNamePkg modulusPkg
  have compactUnary : UnaryHistory compact := carrier.left
  have finiteNetUnary : UnaryHistory finiteNet := carrier.right.left
  have windowsUnary : UnaryHistory windows := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have familyUnary : UnaryHistory family :=
    unary_cont_closed compactUnary finiteNetUnary compactFiniteNet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed familyUnary windowsUnary familyWindows
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have sourceModulus :
      (fun row : BHist =>
        (hsame row windows ∨ hsame row readback ∨ hsame row sealRow ∨ hsame row modulus) ∧
          UnaryHistory row)
        modulus := by
    exact ⟨Or.inr (Or.inr (Or.inr (hsame_refl modulus))), modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row windows ∨ hsame row readback ∨ hsame row sealRow ∨
              hsame row modulus) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨
              hsame row modulus ∨ hsame row windows ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle modulus pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulus sourceModulus
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source with
      | intro sourceRows _sourceUnary =>
          cases sourceRows with
          | inl windowsRow =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl windowsRow))))
          | inr rest₁ =>
              cases rest₁ with
              | inl readbackRow =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inl readbackRow)))))
              | inr rest₂ =>
                  cases rest₂ with
                  | inl sealRowSame =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inl sealRowSame))))))
                  | inr modulusRow =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl modulusRow)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusPkg, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, familyUnary, readbackUnary, modulusUnary⟩

end BEDC.Derived.DiniUniformConvergenceUp
