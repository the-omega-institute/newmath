import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfLowerCutReadbackScope [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic upperSurface terminal transport replay provenance localName
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory upperSurface →
      Cont lowerCut upperSurface dyadic →
      Cont terminal transport sealRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle sealRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperSurface ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont lowerCut upperSurface dyadic ∧ Cont terminal transport sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame ∧
        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _upperSurfaceUnary lowerUpperDyadic terminalTransport provenancePkg sealPkg
  have sequenceUnary : UnaryHistory sequence := carrier.left
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalTransport
  have sequenceLowerDyadic : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have sourceSequence :
      (fun row : BHist =>
        (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic) ∧
          UnaryHistory row) sequence := by
    exact ⟨Or.inl (hsame_refl sequence), sequenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperSurface ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont lowerCut upperSurface dyadic ∧ Cont terminal transport sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sequence sourceSequence
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
          | inl sameSequence =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSequence)
          | inr rest =>
              cases rest with
              | inl sameLower =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLower))
              | inr sameDyadic =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameDyadic))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSequence =>
          exact Or.inl sameSequence
      | inr rest =>
          cases rest with
          | inl sameLower =>
              exact Or.inr (Or.inl sameLower)
          | inr sameDyadic =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sequenceLowerDyadic, lowerUpperDyadic, terminalTransport,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LiminfUp
