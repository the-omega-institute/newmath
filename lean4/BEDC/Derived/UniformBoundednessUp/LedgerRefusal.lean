import BEDC.Derived.UniformBoundednessUp

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessLedgerRefusal [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg ->
      Cont transport replay refusalRead ->
        PkgSig bundle refusalRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row refusalRead ∧
                  UniformBoundednessPacket family pointwise baire norm regseq stream transport
                    history replay provenance nameRow bundle pkg)
              (fun row : BHist =>
                hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨
                  hsame row norm ∨ hsame row regseq ∨ hsame row stream ∨
                    hsame row transport ∨ hsame row history ∨ hsame row replay ∨
                      hsame row provenance ∨ hsame row nameRow ∨ hsame row refusalRead)
              (fun row : BHist =>
                hsame row refusalRead ∧ Cont transport replay refusalRead ∧
                  PkgSig bundle refusalRead pkg)
              hsame ∧
            Cont transport history replay ∧ Cont replay provenance nameRow ∧
              Cont transport replay refusalRead ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro hpacket refusalRoute refusalPkg
  have transportHistoryReplay : Cont transport history replay :=
    hpacket.right.right.right.right.left
  have replayProvenanceNameRow : Cont replay provenance nameRow :=
    hpacket.right.right.right.right.right.left
  have sourceRefusal :
      hsame refusalRead refusalRead ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact ⟨hsame_refl refusalRead, hpacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusalRead ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨ hsame row norm ∨
              hsame row regseq ∨ hsame row stream ∨ hsame row transport ∨
                hsame row history ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row nameRow ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont transport replay refusalRead ∧
              PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, hpacket⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, refusalPkg⟩
  }
  exact ⟨cert, transportHistoryReplay, replayProvenanceNameRow, refusalRoute, refusalPkg⟩

end BEDC.Derived.UniformBoundednessUp
