import BEDC.Derived.CauchyfiltercompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_provenance_exhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      uniformRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow provenance uniformRead →
        Cont uniformRead name terminalRead →
          PkgSig bundle terminalRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row provenance ∨ hsame row uniformRead ∨ hsame row terminalRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row provenance ∨
                      hsame row uniformRead ∨ hsame row terminalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle terminalRead pkg ∧
                    Cont uniformRead name terminalRead)
                hsame ∧
              UnaryHistory uniformRead ∧ UnaryHistory terminalRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sealProvenanceUniform uniformNameTerminal terminalPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, nameUnary, _filterWindowsTolerance,
    _toleranceReadbackSeal, _transportReplayProvenance, provenancePkg, _namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceUniform
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed uniformUnary nameUnary uniformNameTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row provenance ∨ hsame row uniformRead ∨ hsame row terminalRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row provenance ∨
                hsame row uniformRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle terminalRead pkg ∧
              Cont uniformRead name terminalRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨Or.inl (hsame_refl provenance), provenanceUnary⟩
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
        cases source with
        | intro sourceRows sourceUnary =>
            constructor
            · cases sourceRows with
              | inl sameProvenance =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameProvenance)
              | inr rest =>
                  cases rest with
                  | inl sameUniform =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameUniform))
                  | inr sameTerminal =>
                      exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTerminal))
            · exact unary_transport sourceUnary sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameProvenance =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameProvenance)))))
      | inr rest =>
          cases rest with
          | inl sameUniform =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl sameUniform))))))
          | inr sameTerminal =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr sameTerminal))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, terminalPkg, uniformNameTerminal⟩
  }
  exact ⟨cert, uniformUnary, terminalUnary, provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
