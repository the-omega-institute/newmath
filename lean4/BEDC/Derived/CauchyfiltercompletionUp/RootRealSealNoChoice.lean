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

theorem CauchyFilterCompletionPacket_root_real_seal_no_choice [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name admitted regularRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows admitted →
        Cont admitted readback regularRead →
          hsame sealRow sealRead →
            PkgSig bundle regularRead pkg →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row regularRead ∨ hsame row sealRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                        hsame row readback ∨ hsame row sealRow ∨ hsame row regularRead ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
                        Cont admitted readback regularRead)
                    hsame ∧
                  UnaryHistory admitted ∧ UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                    Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet filterWindowsAdmitted admittedReadbackRegular sealSame regularPkg sealPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindowsTolerance,
    toleranceReadbackSeal, _transportReplayProvenance, provenancePkg, _namePkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed filterUnary windowsUnary filterWindowsAdmitted
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed admittedUnary readbackUnary admittedReadbackRegular
  have sealReadUnary : UnaryHistory sealRead :=
    unary_transport sealUnary sealSame
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row regularRead ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row regularRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
              Cont admitted readback regularRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨Or.inr (hsame_refl sealRead), sealReadUnary⟩
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
        constructor
        · cases source.left with
          | inl sameRegular =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRegular)
          | inr sameSeal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRegular =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegular)))))
      | inr sameSeal =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg, admittedReadbackRegular⟩
  }
  exact
    ⟨cert, admittedUnary, regularUnary, sealReadUnary, filterWindowsTolerance,
      toleranceReadbackSeal, provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
