import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_real_seal_refusal [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                  hsame row readback ∨ hsame row sealRow ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont filter windows tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont readback sealRow sealRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
              hsame ∧
            UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
              Cont tolerance readback sealRow ∧ Cont readback sealRow sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet readbackSeal sealReadPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
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
            UnaryHistory row ∧ Cont filter windows tolerance ∧
              Cont tolerance readback sealRow ∧ Cont readback sealRow sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
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
      exact
        ⟨source.right, filterWindows, toleranceReadback, readbackSeal, provenancePkg,
          sealReadPkg⟩
  }
  exact
    ⟨cert, sealReadUnary, filterWindows, toleranceReadback, readbackSeal, provenancePkg,
      sealReadPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
