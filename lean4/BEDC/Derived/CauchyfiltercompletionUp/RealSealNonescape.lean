import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_real_seal_nonescape [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame sealRow sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                  hsame row readback ∨ hsame row sealRow ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
                  Cont filter windows tolerance ∧ Cont tolerance readback sealRow)
              hsame ∧
            UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
              Cont tolerance readback sealRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sameSeal sealReadPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_transport sealUnary sameSeal
  have sourceSealRead :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSealRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealReadPkg, filterWindows, toleranceReadback⟩
  }
  exact ⟨cert, sealReadUnary, filterWindows, toleranceReadback⟩

end BEDC.Derived.CauchyfiltercompletionUp
