import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamnameReindexTerminalCoverage [AskSetup] [PackageSetup]
    {window endpoint dyadic regseq realSeal support route terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window →
      UnaryHistory endpoint →
        UnaryHistory dyadic →
          UnaryHistory regseq →
            UnaryHistory realSeal →
              Cont window endpoint support →
                Cont support dyadic regseq →
                  Cont regseq realSeal terminal →
                    PkgSig bundle terminal pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row terminal ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                          (fun row : BHist =>
                            hsame row window ∨ hsame row dyadic ∨ hsame row regseq ∨
                              hsame row realSeal ∨ hsame row terminal)
                          (fun row : BHist =>
                            hsame row terminal ∧ Cont window endpoint support ∧
                              Cont support dyadic regseq ∧ Cont regseq realSeal terminal)
                          hsame ∧ UnaryHistory support ∧ UnaryHistory terminal ∧
                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: StreamNameUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro windowUnary endpointUnary dyadicUnary _regseqUnary realSealUnary windowEndpointSupport
    supportDyadicRegseq regseqRealTerminal terminalPkg
  have supportUnary : UnaryHistory support :=
    unary_cont_closed windowUnary endpointUnary windowEndpointSupport
  have regseqRouteUnary : UnaryHistory regseq :=
    unary_cont_closed supportUnary dyadicUnary supportDyadicRegseq
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed regseqRouteUnary realSealUnary regseqRealTerminal
  have sourceTerminal :
      (fun row : BHist =>
        hsame row terminal ∧ UnaryHistory row ∧ PkgSig bundle row pkg) terminal := by
    exact ⟨hsame_refl terminal, terminalUnary, terminalPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row terminal ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadic ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row terminal)
          (fun row : BHist =>
            hsame row terminal ∧ Cont window endpoint support ∧
              Cont support dyadic regseq ∧ Cont regseq realSeal terminal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal sourceTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, windowEndpointSupport, supportDyadicRegseq, regseqRealTerminal⟩
  }
  exact ⟨cert, supportUnary, terminalUnary, terminalPkg⟩

end BEDC.Derived.StreamNameUp
