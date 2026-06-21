import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfBoundedCutCompatibilityObligation [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName upperCut cutRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory upperCut →
      Cont lowerCut upperCut cutRead →
      Cont terminal transport sealRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle sealRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerCut ∨ hsame row upperCut ∨ hsame row cutRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperCut ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row cutRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut upperCut cutRead ∧
              Cont terminal transport sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame ∧
        UnaryHistory cutRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier upperCutUnary lowerUpperCut terminalSeal provenancePkg sealPkg
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have cutReadUnary : UnaryHistory cutRead :=
    unary_cont_closed lowerCutUnary upperCutUnary lowerUpperCut
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalSeal
  have lowerSource :
      (fun row : BHist =>
        (hsame row lowerCut ∨ hsame row upperCut ∨ hsame row cutRead ∨
            hsame row sealRead) ∧
          UnaryHistory row) lowerCut := by
    exact ⟨Or.inl (hsame_refl lowerCut), lowerCutUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerCut ∨ hsame row upperCut ∨ hsame row cutRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperCut ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row cutRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut upperCut cutRead ∧
              Cont terminal transport sealRead ∧ PkgSig bundle provenance pkg ∧
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
              | inl sameCutRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inl sameCutRead)))))
              | inr sameSealRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr sameSealRead)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lowerUpperCut, terminalSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, cutReadUnary, sealReadUnary⟩

end BEDC.Derived.LiminfUp
