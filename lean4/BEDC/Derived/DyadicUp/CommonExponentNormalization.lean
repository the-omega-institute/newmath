import BEDC.Derived.DyadicUp.RealSealFactorization

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUpCommonExponentNormalization [AskSetup] [PackageSetup]
    {Q0 S0 R0 E0 H0 C0 P0 N0 Q1 S1 R1 E1 H1 C1 P1 N1 shift0 shift1 commonRead
      seal0 seal1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q0 S0 R0 E0 H0 C0 P0 N0 bundle pkg ->
      DyadicCarrier Q1 S1 R1 E1 H1 C1 P1 N1 bundle pkg ->
        Cont Q0 S0 shift0 -> Cont Q1 S1 shift1 -> Cont shift0 shift1 commonRead ->
          Cont commonRead E0 seal0 -> Cont commonRead E1 seal1 ->
            PkgSig bundle seal0 pkg -> PkgSig bundle seal1 pkg ->
              SemanticNameCert
                  (fun row : BHist => (hsame row seal0 ∨ hsame row seal1) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q0 ∨ hsame row Q1 ∨ hsame row S0 ∨ hsame row S1 ∨
                      hsame row shift0 ∨ hsame row shift1 ∨ hsame row commonRead ∨
                        hsame row seal0 ∨ hsame row seal1)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Q0 S0 shift0 ∧ Cont Q1 S1 shift1 ∧
                      Cont shift0 shift1 commonRead ∧ Cont commonRead E0 seal0 ∧
                        Cont commonRead E1 seal1 ∧ PkgSig bundle seal0 pkg ∧
                          PkgSig bundle seal1 pkg)
                  hsame ∧ UnaryHistory shift0 ∧ UnaryHistory shift1 ∧
                    UnaryHistory commonRead ∧ UnaryHistory seal0 ∧
                      UnaryHistory seal1 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier0 carrier1 shiftRoute0 shiftRoute1 commonRoute sealRoute0 sealRoute1
    sealPkg0 sealPkg1
  obtain ⟨q0Unary, s0Unary, _r0Unary, e0Unary, _h0Unary, _c0Unary, _p0Unary,
    _n0Unary, _qsrRoute0, _recRoute0, _provenancePkg0, _namePkg0⟩ := carrier0
  obtain ⟨q1Unary, s1Unary, _r1Unary, e1Unary, _h1Unary, _c1Unary, _p1Unary,
    _n1Unary, _qsrRoute1, _recRoute1, _provenancePkg1, _namePkg1⟩ := carrier1
  have shiftUnary0 : UnaryHistory shift0 :=
    unary_cont_closed q0Unary s0Unary shiftRoute0
  have shiftUnary1 : UnaryHistory shift1 :=
    unary_cont_closed q1Unary s1Unary shiftRoute1
  have commonUnary : UnaryHistory commonRead :=
    unary_cont_closed shiftUnary0 shiftUnary1 commonRoute
  have sealUnary0 : UnaryHistory seal0 :=
    unary_cont_closed commonUnary e0Unary sealRoute0
  have sealUnary1 : UnaryHistory seal1 :=
    unary_cont_closed commonUnary e1Unary sealRoute1
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row seal0 ∨ hsame row seal1) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q0 ∨ hsame row Q1 ∨ hsame row S0 ∨ hsame row S1 ∨
              hsame row shift0 ∨ hsame row shift1 ∨ hsame row commonRead ∨
                hsame row seal0 ∨ hsame row seal1)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q0 S0 shift0 ∧ Cont Q1 S1 shift1 ∧
              Cont shift0 shift1 commonRead ∧ Cont commonRead E0 seal0 ∧
                Cont commonRead E1 seal1 ∧ PkgSig bundle seal0 pkg ∧
                  PkgSig bundle seal1 pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro seal0 ⟨Or.inl (hsame_refl seal0), sealUnary0⟩
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
          | inl sameSeal0 =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSeal0)
          | inr sameSeal1 =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal1)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSeal0 =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameSeal0)))))))
      | inr sameSeal1 =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr sameSeal1)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, shiftRoute0, shiftRoute1, commonRoute, sealRoute0, sealRoute1,
          sealPkg0, sealPkg1⟩
  }
  exact ⟨cert, shiftUnary0, shiftUnary1, commonUnary, sealUnary0, sealUnary1⟩

end BEDC.Derived.DyadicUp
