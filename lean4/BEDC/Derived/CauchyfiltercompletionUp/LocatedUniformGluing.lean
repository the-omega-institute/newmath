import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_located_uniform_gluing [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name locatedRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow locatedRead →
        Cont transport replay uniformRead →
          PkgSig bundle locatedRead pkg →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row locatedRead ∨ hsame row uniformRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row locatedRead ∨ hsame row uniformRead)
                  (fun row : BHist =>
                    (hsame row locatedRead ∨ hsame row uniformRead) ∧
                      PkgSig bundle row pkg)
                  hsame ∧
                UnaryHistory locatedRead ∧ UnaryHistory uniformRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet locatedRoute uniformRoute locatedPkg uniformPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed readbackUnary sealUnary locatedRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed transportUnary replayUnary uniformRoute
  have sourceLocated :
      (fun row : BHist =>
        (hsame row locatedRead ∨ hsame row uniformRead) ∧ UnaryHistory row) locatedRead := by
    exact ⟨Or.inl (hsame_refl locatedRead), locatedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row locatedRead ∨ hsame row uniformRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
              hsame row replay ∨ hsame row locatedRead ∨ hsame row uniformRead)
          (fun row : BHist =>
            (hsame row locatedRead ∨ hsame row uniformRead) ∧ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead sourceLocated
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
        cases source.left with
        | inl sameLocated =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameLocated),
                unary_transport source.right sameRows⟩
        | inr sameUniform =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameUniform),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLocated =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameLocated
      | inr sameUniform =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr sameUniform
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameLocated =>
          cases sameLocated
          exact ⟨Or.inl (hsame_refl locatedRead), locatedPkg⟩
      | inr sameUniform =>
          cases sameUniform
          exact ⟨Or.inr (hsame_refl uniformRead), uniformPkg⟩
  }
  exact ⟨cert, locatedUnary, uniformUnary, provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
