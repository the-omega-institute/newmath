import BEDC.Derived.CauchyEquivalenceSetoidUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidNoQuotient [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name quotientAttempt :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow quotientAttempt →
        PkgSig bundle quotientAttempt pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                      hsame row quotientAttempt) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                  hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                    hsame row quotientAttempt)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont test sealRow quotientAttempt ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle quotientAttempt pkg)
              hsame ∧
            UnaryHistory quotientAttempt := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier testSealQuotient quotientPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrier
  have quotientUnary : UnaryHistory quotientAttempt :=
    unary_cont_closed testUnary sealUnary testSealQuotient
  have quotientPattern :
      hsame quotientAttempt s0 ∨ hsame quotientAttempt s1 ∨ hsame quotientAttempt r0 ∨
        hsame quotientAttempt r1 ∨ hsame quotientAttempt dyadic ∨
          hsame quotientAttempt test ∨ hsame quotientAttempt sealRow ∨
            hsame quotientAttempt quotientAttempt := by
    right
    right
    right
    right
    right
    right
    right
    exact hsame_refl quotientAttempt
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                  hsame row quotientAttempt) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row quotientAttempt)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow quotientAttempt ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                PkgSig bundle quotientAttempt pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro quotientAttempt ⟨quotientPattern, quotientUnary⟩
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
          | inl sameS0 =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameS0)
          | inr rest =>
              cases rest with
              | inl sameS1 =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameS1))
              | inr rest =>
                  cases rest with
                  | inl sameR0 =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR0)))
                  | inr rest =>
                      cases rest with
                      | inl sameR1 =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR1))))
                      | inr rest =>
                          cases rest with
                          | inl sameDyadic =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameDyadic)))))
                          | inr rest =>
                              cases rest with
                              | inl sameTest =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameTest))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameSeal =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameSeal)))))))
                                  | inr sameQuotient =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameQuotient)))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, testSealQuotient, provenancePkg, namePkg, quotientPkg⟩
  }
  exact ⟨cert, quotientUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
