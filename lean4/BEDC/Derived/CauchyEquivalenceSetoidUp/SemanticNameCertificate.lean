import BEDC.Derived.CauchyEquivalenceSetoidUp

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow sealRead →
        Cont sealRead replay equalityRead →
          PkgSig bundle equalityRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row sealRead ∨ hsame row equalityRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                      hsame row sealRead ∨ hsame row equalityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont test sealRow sealRead ∧
                    Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg)
                hsame ∧
              UnaryHistory sealRead ∧ UnaryHistory equalityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier sealRoute equalityRoute equalityPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary, sealUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed sealReadUnary replayUnary equalityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sealRead ∨ hsame row equalityRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row sealRead ∨ hsame row equalityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro equalityRead ⟨Or.inr (hsame_refl equalityRead), equalityReadUnary⟩
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
        | inl sameSeal =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSeal),
                unary_transport source.right sameRows⟩
        | inr sameEquality =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameEquality),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSeal =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sameSeal)))))))
      | inr sameEquality =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sameEquality)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, equalityRoute, provenancePkg, namePkg, equalityPkg⟩
  }
  exact ⟨cert, sealReadUnary, equalityReadUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
