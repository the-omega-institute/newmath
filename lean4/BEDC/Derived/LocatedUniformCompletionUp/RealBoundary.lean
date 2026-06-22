import BEDC.Derived.LocatedUniformCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedUniformCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedUniformCompletionCarrier [AskSetup] [PackageSetup] (F U B S R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory B ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LocatedUniformCompletionRealBoundary [AskSetup] [PackageSetup]
    {F U B S R E H C P N filterUniform regularWindow realRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedUniformCompletionCarrier F U B S R E H C P N bundle pkg →
      Cont F U filterUniform →
        Cont B S regularWindow →
          Cont regularWindow E realRead →
            Cont realRead H boundaryRead →
              PkgSig bundle boundaryRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
                        hsame row R ∨ hsame row E ∨ hsame row boundaryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F U filterUniform ∧
                        Cont B S regularWindow ∧ Cont regularWindow E realRead ∧
                          Cont realRead H boundaryRead ∧ PkgSig bundle boundaryRead pkg)
                    hsame ∧
                  UnaryHistory filterUniform ∧
                    UnaryHistory regularWindow ∧
                      UnaryHistory realRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: LocatedUniformCompletionUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier filterRoute regularRoute realRoute boundaryRoute boundaryPkg
  rcases carrier with
    ⟨unaryF, unaryU, unaryB, unaryS, _unaryR, unaryE, unaryH, _unaryC, _unaryP,
      _unaryN, _provenancePkg, _namePkg⟩
  have filterUnary : UnaryHistory filterUniform :=
    unary_cont_closed unaryF unaryU filterRoute
  have regularUnary : UnaryHistory regularWindow :=
    unary_cont_closed unaryB unaryS regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary unaryE realRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed realUnary unaryH boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F U filterUniform ∧ Cont B S regularWindow ∧
              Cont regularWindow E realRead ∧ Cont realRead H boundaryRead ∧
                PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact ⟨source.right, filterRoute, regularRoute, realRoute, boundaryRoute, boundaryPkg⟩
  }
  exact ⟨cert, filterUnary, regularUnary, realUnary, boundaryUnary⟩

end BEDC.Derived.LocatedUniformCompletionUp
