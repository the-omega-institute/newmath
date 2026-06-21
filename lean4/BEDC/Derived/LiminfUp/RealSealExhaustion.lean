import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfRealSealExhaustionObligation [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead
      valueRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      Cont terminal transport sealRead →
        Cont sealRead localName valueRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle valueRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row terminal ∨ hsame row sealRead ∨ hsame row valueRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                      hsame row terminal ∨ hsame row sealRead ∨ hsame row valueRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont terminal transport sealRead ∧
                      Cont sealRead localName valueRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle valueRead pkg)
                  hsame ∧
                UnaryHistory sealRead ∧ UnaryHistory valueRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier terminalSeal sealValue provenancePkg valuePkg
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have localNameUnary : UnaryHistory localName :=
    carrier.right.right.right.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalSeal
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sealUnary localNameUnary sealValue
  have valueSource :
      (fun row : BHist =>
        (hsame row terminal ∨ hsame row sealRead ∨ hsame row valueRead) ∧
          UnaryHistory row) valueRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl valueRead)), valueUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row terminal ∨ hsame row sealRead ∨ hsame row valueRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead ∨ hsame row valueRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont terminal transport sealRead ∧
              Cont sealRead localName valueRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle valueRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro valueRead valueSource
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
          | inl sameTerminal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal)
          | inr rest =>
              cases rest with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))
              | inr sameValue =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameValue))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameTerminal =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameTerminal)))
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSeal))))
          | inr sameValue =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameValue))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, terminalSeal, sealValue, provenancePkg, valuePkg⟩
  }
  exact ⟨cert, sealUnary, valueUnary⟩

end BEDC.Derived.LiminfUp
