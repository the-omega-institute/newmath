import BEDC.Derived.DiniUniformConvergenceUp.NameCertObligations

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiniUniformConvergenceCarrier_monotone_window_obligation [AskSetup] [PackageSetup]
    {compact finiteNet family modulus windows readback sealRow transportRow replayRow provenance
      localName monotoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier compact finiteNet family modulus windows readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont compact finiteNet family ->
        Cont family windows readback ->
          Cont readback sealRow monotoneRead ->
            PkgSig bundle localName pkg ->
              PkgSig bundle monotoneRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row monotoneRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row family ∨ hsame row windows ∨ hsame row readback ∨
                        hsame row sealRow ∨ hsame row monotoneRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle monotoneRead pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory monotoneRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactFiniteNet familyWindows readbackSeal localNamePkg monotonePkg
  obtain ⟨compactUnary, finiteNetUnary, windowsUnary, sealUnary, provenancePkg⟩ := carrier
  have familyUnary : UnaryHistory family :=
    unary_cont_closed compactUnary finiteNetUnary compactFiniteNet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed familyUnary windowsUnary familyWindows
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have sourceMonotone :
      (fun row : BHist => hsame row monotoneRead ∧ UnaryHistory row) monotoneRead := by
    exact ⟨hsame_refl monotoneRead, monotoneUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row monotoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row windows ∨ hsame row readback ∨
              hsame row sealRow ∨ hsame row monotoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle monotoneRead pkg ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro monotoneRead sourceMonotone
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, monotonePkg, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, monotoneUnary⟩

end BEDC.Derived.DiniUniformConvergenceUp
