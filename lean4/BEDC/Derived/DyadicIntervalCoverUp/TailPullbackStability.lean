import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverTailPullbackStability [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont windowRead sealRead tailRead →
              PkgSig bundle tailRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
                        hsame row A ∨ hsame row windowRead ∨ hsame row sealRead ∨
                          hsame row tailRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
                        Cont coverRead A sealRead ∧ Cont windowRead sealRead tailRead ∧
                          PkgSig bundle tailRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory coverRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro surface windowCont coverCont sealCont tailCont tailPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary sealUnary tailCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
              hsame row A ∨ hsame row windowRead ∨ hsame row sealRead ∨
                hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
              Cont coverRead A sealRead ∧ Cont windowRead sealRead tailRead ∧
                PkgSig bundle tailRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowCont, coverCont, sealCont, tailCont, tailPkg⟩
  }
  exact ⟨cert, windowUnary, coverUnary, sealUnary, tailUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
