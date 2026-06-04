import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRealSealCoverHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => (hsame row sealRead ∨ hsame row namedRead) ∧
                      UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
                        hsame row V ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row sealRead ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
                        Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                          PkgSig bundle namedRead pkg)
                    hsame ∧ UnaryHistory windowRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface windowRoute coverRoute sealRoute namedRoute namedPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row sealRead ∨ hsame row namedRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
              Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨Or.inr (hsame_refl namedRead), namedUnary⟩
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
          | inl sameSeal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
          | inr sameNamed =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameNamed)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSeal =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl sameSeal))))))))))
      | inr sameNamed =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sameNamed))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, coverRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, windowUnary, coverUnary, sealUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
