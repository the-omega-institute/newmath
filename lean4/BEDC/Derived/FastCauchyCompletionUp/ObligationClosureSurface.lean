import BEDC.Derived.FastCauchyCompletionUp.FiniteInduction

namespace BEDC.Derived.FastCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchyCompletionObligationClosureSurface [AskSetup] [PackageSetup]
    {modulus stream dyadic readback sealRow transport replay provenance localName tailRead
      terminalRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyCompletionCarrier modulus stream dyadic readback sealRow transport replay provenance
        localName bundle pkg ->
      Cont modulus stream tailRead ->
        Cont tailRead dyadic readback ->
          Cont readback sealRow terminalRead ->
            Cont terminalRead localName closureRead ->
              PkgSig bundle closureRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
                        hsame row readback ∨ hsame row sealRow ∨ hsame row terminalRead ∨
                          hsame row closureRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont modulus stream tailRead ∧
                        Cont tailRead dyadic readback ∧ Cont readback sealRow terminalRead ∧
                          Cont terminalRead localName closureRead ∧
                            PkgSig bundle closureRead pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ UnaryHistory terminalRead ∧
                    UnaryHistory closureRead ∧ PkgSig bundle closureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier modulusStreamTail tailDyadicReadback readbackSealTerminal
    terminalLocalClosure closurePkg
  obtain ⟨modulusUnary, streamUnary, dyadicUnary, readbackUnary, sealUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _sealPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed modulusUnary streamUnary modulusStreamTail
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealTerminal
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed terminalUnary localNameUnary terminalLocalClosure
  have sourceClosure :
      (fun row : BHist => hsame row closureRead ∧ UnaryHistory row) closureRead := by
    exact ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row terminalRead ∨
                hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus stream tailRead ∧
              Cont tailRead dyadic readback ∧ Cont readback sealRow terminalRead ∧
                Cont terminalRead localName closureRead ∧ PkgSig bundle closureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceClosure
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, modulusStreamTail, tailDyadicReadback, readbackSealTerminal,
          terminalLocalClosure, closurePkg⟩
  }
  exact ⟨cert, tailUnary, terminalUnary, closureUnary, closurePkg⟩

end BEDC.Derived.FastCauchyCompletionUp
