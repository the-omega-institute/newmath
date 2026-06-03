import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicIntervalCoverRootObligationSurface [AskSetup] [PackageSetup]
    (L U M R V W Q A H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory L ∧
    UnaryHistory U ∧
      UnaryHistory M ∧
        UnaryHistory R ∧
          UnaryHistory V ∧
            UnaryHistory W ∧
              UnaryHistory Q ∧
                UnaryHistory A ∧
                  UnaryHistory H ∧
                    UnaryHistory C ∧
                      UnaryHistory P ∧
                        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem DyadicIntervalCoverRootWindowCoverage [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory windowRead ∧
                UnaryHistory coverRead ∧ UnaryHistory sealRead ∧ Cont W Q windowRead ∧
                  Cont M R coverRead ∧ Cont coverRead A sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface windowCont coverCont sealCont sealPkg
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  exact
    ⟨wUnary, qUnary, windowUnary, coverUnary, sealUnary, windowCont, coverCont, sealCont,
      pPkg, sealPkg⟩

theorem DyadicIntervalCoverRegularWindowLedger [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
                      hsame row V ∨ hsame row A ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
                      Cont coverRead A sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧ UnaryHistory windowRead ∧ UnaryHistory coverRead ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface windowCont coverCont sealCont sealPkg
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row A ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
              Cont coverRead A sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowCont, coverCont, sealCont, sealPkg⟩
  }
  exact ⟨cert, windowUnary, coverUnary, sealUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
