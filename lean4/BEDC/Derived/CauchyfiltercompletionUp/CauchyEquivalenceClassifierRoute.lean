import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionCauchyEquivalenceClassifierRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name equivalenceRead
      separatedRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont windows readback equivalenceRead ->
        Cont equivalenceRead sealRow separatedRead ->
          Cont separatedRead provenance completionRead ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row windows ∨ hsame row readback ∨ hsame row tolerance ∨
                        hsame row sealRow ∨ hsame row equivalenceRead ∨
                          hsame row separatedRead ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont windows readback equivalenceRead ∧
                        Cont equivalenceRead sealRow separatedRead ∧
                          Cont separatedRead provenance completionRead ∧
                            PkgSig bundle completionRead pkg)
                    hsame ∧
                UnaryHistory equivalenceRead ∧ UnaryHistory separatedRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: CauchyFilterCompletionPacket BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet equivalenceRoute separatedRoute completionRoute completionPkg
  obtain ⟨_filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have equivalenceUnary : UnaryHistory equivalenceRead :=
    unary_cont_closed windowsUnary readbackUnary equivalenceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed equivalenceUnary sealUnary separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary provenanceUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windows ∨ hsame row readback ∨ hsame row tolerance ∨
              hsame row sealRow ∨ hsame row equivalenceRead ∨ hsame row separatedRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windows readback equivalenceRead ∧
              Cont equivalenceRead sealRow separatedRead ∧
                Cont separatedRead provenance completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, equivalenceRoute, separatedRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, equivalenceUnary, separatedUnary, completionUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
