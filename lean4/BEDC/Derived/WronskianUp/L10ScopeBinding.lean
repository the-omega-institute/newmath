import BEDC.Derived.WronskianUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WronskianCarrier [AskSetup] [PackageSetup]
    (F D J Omega S R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory F ∧ UnaryHistory D ∧ UnaryHistory J ∧ UnaryHistory Omega ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont F D J ∧
        Cont J Omega E ∧ Cont S R E ∧ Cont E H C ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem WronskianCarrier_l10_scope_binding [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianCarrier F D J Omega S R E H C P N bundle pkg ->
      Cont E H l10Read ->
        PkgSig bundle l10Read pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
                  hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row l10Read)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont E H l10Read ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle l10Read pkg)
              hsame ∧
            UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier l10Route l10Pkg
  obtain ⟨_fUnary, _dUnary, _jUnary, _omegaUnary, _sUnary, _rUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _familyRoute, _determinantRoute, _valueRoute,
    _scopeRoute, provenancePkg, _namePkg⟩ := carrier
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed eUnary hUnary l10Route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E H l10Read ∧ PkgSig bundle P pkg ∧
              PkgSig bundle l10Read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Read ⟨hsame_refl l10Read, l10Unary⟩
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, l10Route, provenancePkg, l10Pkg⟩
  }
  exact ⟨cert, l10Unary⟩

end BEDC.Derived.WronskianUp
