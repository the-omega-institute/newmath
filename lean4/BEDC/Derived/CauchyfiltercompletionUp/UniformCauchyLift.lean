import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionUniformCauchyLift [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name admitted
      uniformRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows admitted →
        Cont admitted tolerance uniformRead →
          Cont uniformRead readback sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      (hsame row admitted ∨ hsame row uniformRead ∨ hsame row sealRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                        hsame row readback ∨ hsame row admitted ∨ hsame row uniformRead ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
                        Cont uniformRead readback sealRead)
                    hsame ∧
                UnaryHistory admitted ∧ UnaryHistory uniformRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet filterWindowsAdmitted admittedToleranceUniform uniformReadbackSeal sealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed filterUnary windowsUnary filterWindowsAdmitted
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed admittedUnary toleranceUnary admittedToleranceUniform
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed uniformUnary readbackUnary uniformReadbackSeal
  have sourceAdmitted :
      (fun row : BHist =>
        (hsame row admitted ∨ hsame row uniformRead ∨ hsame row sealRead) ∧
          UnaryHistory row) admitted := by
    exact ⟨Or.inl (hsame_refl admitted), admittedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row admitted ∨ hsame row uniformRead ∨ hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row admitted ∨ hsame row uniformRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
              Cont uniformRead readback sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro admitted sourceAdmitted
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
        have shifted :
            hsame _other admitted ∨ hsame _other uniformRead ∨ hsame _other sealRead := by
          cases source.left with
          | inl sameAdmitted =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameAdmitted)
          | inr rest =>
              cases rest with
              | inl sameUniform =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameUniform))
              | inr sameSeal =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))
        exact ⟨shifted, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameAdmitted =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameAdmitted))))
      | inr rest =>
          cases rest with
          | inl sameUniform =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameUniform)))))
          | inr sameSeal =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg, uniformReadbackSeal⟩
  }
  exact ⟨cert, admittedUnary, uniformUnary, sealUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
