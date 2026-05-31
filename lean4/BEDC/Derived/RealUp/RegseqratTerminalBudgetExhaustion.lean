import BEDC.Derived.RealUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealRegseqratTerminalBudgetExhaustion [AskSetup] [PackageSetup]
    {dyadic stream regseq realSeal terminalRead support provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        UnaryHistory regseq ->
          UnaryHistory realSeal ->
            Cont dyadic stream regseq ->
              Cont regseq realSeal terminalRead ->
                Cont support localName terminalRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle terminalRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                              hsame row realSeal ∨ hsame row terminalRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont dyadic stream regseq ∧
                              Cont regseq realSeal terminalRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle terminalRead pkg)
                          hsame ∧
                        UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _dyadicUnary _streamUnary regseqUnary realSealUnary dyadicStreamRegseq
    regseqRealTerminal _supportLocalTerminal provenancePkg terminalPkg
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal terminalRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceTerminal
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
      exact
        ⟨source.right, dyadicStreamRegseq, regseqRealTerminal, provenancePkg,
          terminalPkg⟩
  }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.RealUp
