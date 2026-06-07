import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverLedgerExactness [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead radiusRead membershipRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont windowRead R radiusRead →
          Cont radiusRead V membershipRead →
            Cont membershipRead A sealRead →
              PkgSig bundle P pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row membershipRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                        hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                          hsame row membershipRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W Q windowRead ∧
                        Cont windowRead R radiusRead ∧ Cont radiusRead V membershipRead ∧
                          Cont membershipRead A sealRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory membershipRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface windowCont radiusCont membershipCont sealCont pPkg
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed windowUnary rUnary radiusCont
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed radiusUnary vUnary membershipCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed membershipUnary aUnary sealCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row membershipRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row membershipRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W Q windowRead ∧ Cont windowRead R radiusRead ∧
              Cont radiusRead V membershipRead ∧ Cont membershipRead A sealRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro membershipRead ⟨hsame_refl membershipRead, membershipUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowCont, radiusCont, membershipCont, sealCont, pPkg⟩
  }
  exact ⟨cert, membershipUnary, sealUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
