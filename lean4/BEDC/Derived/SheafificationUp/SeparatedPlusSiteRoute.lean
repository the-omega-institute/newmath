import BEDC.Derived.SheafificationUp.TasteGate

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSeparatedPlusSiteRoute [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      PkgSig bundle N pkg →
        SemanticNameCert
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier pkgSig
  obtain ⟨cUnary, tUnary, jUnary, pUnary, lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  let sourceSpec : BHist → Prop :=
    fun row : BHist =>
      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L
  let patternSpec : BHist → Prop :=
    fun row : BHist =>
      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
        hsame row G ∨ hsame row S
  let ledgerPolicy : BHist → Prop :=
    fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg
  have sourceC : sourceSpec C := Or.inl (hsame_refl C)
  have sourceUnary :
      ∀ {row : BHist}, sourceSpec row → UnaryHistory row := by
    intro row source
    cases source with
    | inl sameC => exact unary_transport cUnary (hsame_symm sameC)
    | inr restT =>
        cases restT with
        | inl sameT => exact unary_transport tUnary (hsame_symm sameT)
        | inr restJ =>
            cases restJ with
            | inl sameJ => exact unary_transport jUnary (hsame_symm sameJ)
            | inr restP =>
                cases restP with
                | inl sameP => exact unary_transport pUnary (hsame_symm sameP)
                | inr sameL => exact unary_transport lUnary (hsame_symm sameL)
  exact {
    core := {
      carrier_inhabited := Exists.intro C sourceC
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
        intro row other sameRows source
        cases source with
        | inl sameC =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameC)
        | inr restT =>
            cases restT with
            | inl sameT =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameT))
            | inr restJ =>
                cases restJ with
                | inl sameJ =>
                    exact Or.inr (Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameJ)))
                | inr restP =>
                    cases restP with
                    | inl sameP =>
                        exact Or.inr (Or.inr (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameP))))
                    | inr sameL =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr
                          (hsame_trans (hsame_symm sameRows) sameL))))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameC => exact Or.inl sameC
      | inr restT =>
          cases restT with
          | inl sameT => exact Or.inr (Or.inl sameT)
          | inr restJ =>
              cases restJ with
              | inl sameJ => exact Or.inr (Or.inr (Or.inl sameJ))
              | inr restP =>
                  cases restP with
                  | inl sameP => exact Or.inr (Or.inr (Or.inr (Or.inl sameP)))
                  | inr sameL =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameL))))
    ledger_sound := by
      intro row source
      exact And.intro (sourceUnary source) pkgSig
  }

end BEDC.Derived.SheafificationUp
