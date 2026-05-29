import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_cofinal_regular_readback [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name cofinalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance cofinalRead →
        Cont cofinalRead readback sealRow →
          PkgSig bundle cofinalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row cofinalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ Cont windows tolerance cofinalRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle cofinalRead pkg ∧
                    hsame row cofinalRead)
                hsame ∧
              UnaryHistory cofinalRead ∧ Cont windows tolerance cofinalRead ∧
                Cont cofinalRead readback sealRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet windowsTolerance cofinalReadback cofinalPkg
  obtain ⟨_filterUnary, windowsUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cofinalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ Cont windows tolerance cofinalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle cofinalRead pkg ∧
              hsame row cofinalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cofinalRead ⟨hsame_refl cofinalRead, cofinalUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other cofinalRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr windowsTolerance)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, cofinalPkg, source.left⟩
  }
  exact ⟨cert, cofinalUnary, windowsTolerance, cofinalReadback⟩

end BEDC.Derived.CauchyfiltercompletionUp
