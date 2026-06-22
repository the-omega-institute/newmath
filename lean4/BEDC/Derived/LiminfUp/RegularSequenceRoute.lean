import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfRegularSequenceRoute [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead
      regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg ->
      Cont terminal transport sealRead ->
        Cont sequence dyadic regularRead ->
          PkgSig bundle provenance pkg ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                      hsame row regularRead ∨ hsame row sealRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                      hsame row terminal ∨ hsame row regularRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
                      Cont sequence dyadic regularRead ∧ Cont terminal transport sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier terminalSeal sequenceRegular provenancePkg sealPkg
  have sequenceUnary : UnaryHistory sequence := carrier.left
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sequenceUnary dyadicUnary sequenceRegular
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalSeal
  have sequenceRoute : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have source :
      (fun row : BHist =>
        (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
          hsame row regularRead ∨ hsame row sealRead) ∧ UnaryHistory row) regularRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl regularRead)))), regularUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row regularRead ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row regularRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont sequence dyadic regularRead ∧ Cont terminal transport sealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro regularRead source
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
          intro _row _other sameRows sourceRows
          constructor
          · cases sourceRows.left with
            | inl sameSequence =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSequence)
            | inr rest =>
                cases rest with
                | inl sameLowerCut =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLowerCut))
                | inr rest =>
                    cases rest with
                    | inl sameDyadic =>
                        exact
                          Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)))
                    | inr rest =>
                        cases rest with
                        | inl sameRegular =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameRegular))))
                        | inr sameSeal =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))))
          · exact unary_transport sourceRows.right sameRows
      }
      pattern_sound := by
        intro _row sourceRows
        cases sourceRows.left with
        | inl sameSequence =>
            exact Or.inl sameSequence
        | inr rest =>
            cases rest with
            | inl sameLowerCut =>
                exact Or.inr (Or.inl sameLowerCut)
            | inr rest =>
                cases rest with
                | inl sameDyadic =>
                    exact Or.inr (Or.inr (Or.inl sameDyadic))
                | inr rest =>
                    cases rest with
                    | inl sameRegular =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegular))))
                    | inr sameSeal =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal))))
      ledger_sound := by
        intro _row sourceRows
        exact ⟨sourceRows.right, sequenceRoute, sequenceRegular, terminalSeal, provenancePkg, sealPkg⟩
    }
  exact ⟨cert, regularUnary, sealUnary⟩

end BEDC.Derived.LiminfUp
