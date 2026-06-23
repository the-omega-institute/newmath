import BEDC.Derived.MinimalTriggerHomologyCoreUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MinimalTriggerHomologyCoreUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MinimalTriggerHomologyCoreCarrier [AskSetup] [PackageSetup]
    (Q F N R B K T H C P L : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory Q ∧ UnaryHistory F ∧ UnaryHistory N ∧ UnaryHistory R ∧
    UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory T ∧ UnaryHistory H ∧
      UnaryHistory C ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg

theorem MinimalTriggerHomologyCoreNamecertObligations [AskSetup] [PackageSetup]
    {Q F N R B K T H C P L supportRead boundaryRead homologyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinimalTriggerHomologyCoreCarrier Q F N R B K T H C P L bundle pkg ->
      Cont Q F supportRead ->
        Cont supportRead N boundaryRead ->
          Cont boundaryRead R homologyRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row homologyRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row F ∨ hsame row N ∨ hsame row R ∨
                      hsame row B ∨ hsame row K ∨ hsame row T ∨
                        hsame row homologyRead)
                  (fun row : BHist =>
                    hsame row homologyRead ∧ Cont Q F supportRead ∧
                      Cont supportRead N boundaryRead ∧
                        Cont boundaryRead R homologyRead ∧ PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory homologyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier supportRoute boundaryRoute homologyRoute pkgSig
  rcases carrier with
    ⟨qUnary, fUnary, nUnary, rUnary, _bUnary, _kUnary, _tUnary, _hUnary, _cUnary,
      _pPkg, _lPkg⟩
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed qUnary fUnary supportRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed supportUnary nUnary boundaryRoute
  have homologyUnary : UnaryHistory homologyRead :=
    unary_cont_closed boundaryUnary rUnary homologyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row homologyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row N ∨ hsame row R ∨
              hsame row B ∨ hsame row K ∨ hsame row T ∨ hsame row homologyRead)
          (fun row : BHist =>
            hsame row homologyRead ∧ Cont Q F supportRead ∧
              Cont supportRead N boundaryRead ∧ Cont boundaryRead R homologyRead ∧
                PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro homologyRead ⟨hsame_refl homologyRead, homologyUnary⟩
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
          · exact hsame_trans (hsame_symm sameRows) source.left
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, supportRoute, boundaryRoute, homologyRoute, pkgSig⟩
    }
  exact ⟨cert, homologyUnary⟩

end BEDC.Derived.MinimalTriggerHomologyCoreUp
