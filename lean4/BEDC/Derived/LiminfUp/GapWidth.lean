import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfTailLowerUpperGapWidth [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName upperEnvelope gapRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg ->
      UnaryHistory upperEnvelope ->
      Cont lowerCut upperEnvelope gapRead ->
      Cont gapRead dyadic sealRead ->
      PkgSig bundle provenance pkg ->
      PkgSig bundle sealRead pkg ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row gapRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperEnvelope ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row gapRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut upperEnvelope gapRead ∧
              Cont gapRead dyadic sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame ∧
        UnaryHistory gapRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier upperEnvelopeUnary lowerUpperGap gapSeal provenancePkg sealPkg
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed lowerCutUnary upperEnvelopeUnary lowerUpperGap
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed gapReadUnary dyadicUnary gapSeal
  have lowerSource :
      (fun row : BHist =>
        (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row gapRead ∨
            hsame row sealRead) ∧
          UnaryHistory row) lowerCut := by
    exact ⟨Or.inl (hsame_refl lowerCut), lowerCutUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row gapRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperEnvelope ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row gapRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut upperEnvelope gapRead ∧
              Cont gapRead dyadic sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lowerCut lowerSource
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
      cases source.left with
      | inl sameLower =>
          exact Or.inr (Or.inl sameLower)
      | inr rest₁ =>
          cases rest₁ with
          | inl sameUpper =>
              exact Or.inr (Or.inr (Or.inl sameUpper))
          | inr rest₂ =>
              cases rest₂ with
              | inl sameGap =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inl sameGap)))))
              | inr sameSeal =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr sameSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lowerUpperGap, gapSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, gapReadUnary, sealReadUnary⟩

end BEDC.Derived.LiminfUp
