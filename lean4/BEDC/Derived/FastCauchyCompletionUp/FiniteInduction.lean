import BEDC.Derived.FastCauchyCompletionUp.ModulusRealSeal

namespace BEDC.Derived.FastCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchyCompletionCarrier [AskSetup] [PackageSetup]
    (modulus stream dyadic readback sealRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory modulus ∧ UnaryHistory stream ∧ UnaryHistory dyadic ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle sealRow pkg

theorem FastCauchyCompletion_precision_tail_finite_induction [AskSetup] [PackageSetup]
    {modulus stream dyadic readback sealRow transport replay provenance localName tailRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyCompletionCarrier modulus stream dyadic readback sealRow transport replay provenance
        localName bundle pkg ->
      Cont modulus stream tailRead ->
        Cont tailRead dyadic readback ->
          Cont readback sealRow terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
                      hsame row readback ∨ hsame row terminalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont modulus stream tailRead ∧
                      Cont tailRead dyadic readback ∧ Cont readback sealRow terminalRead ∧
                        PkgSig bundle terminalRead pkg)
                  hsame ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier modulusStreamTail tailDyadicReadback readbackSealTerminal terminalPkg
  obtain ⟨modulusUnary, streamUnary, _dyadicUnary, readbackUnary, sealUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _sealPkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed modulusUnary streamUnary modulusStreamTail
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row readback ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus stream tailRead ∧ Cont tailRead dyadic readback ∧
              Cont readback sealRow terminalRead ∧ PkgSig bundle terminalRead pkg)
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, modulusStreamTail, tailDyadicReadback, readbackSealTerminal,
          terminalPkg⟩
  }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.FastCauchyCompletionUp
