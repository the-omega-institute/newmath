import BEDC.Derived.NormedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_transport_completion_service [AskSetup] [PackageSetup]
    {V R N M Q H T P C V' R' N' M' Q' serviceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      hsame V V' →
        hsame R R' →
          hsame N N' →
            hsame M M' →
              hsame Q Q' →
                Cont Q H serviceRead →
                  PkgSig bundle serviceRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row serviceRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row V' ∨ hsame row R' ∨ hsame row N' ∨ hsame row M' ∨
                            hsame row Q' ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                              hsame row C ∨ hsame row serviceRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont Q H serviceRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle serviceRead pkg)
                        hsame ∧
                      UnaryHistory V' ∧ UnaryHistory R' ∧ UnaryHistory N' ∧
                        UnaryHistory M' ∧ UnaryHistory Q' ∧ UnaryHistory serviceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sameV sameR sameN sameM sameQ serviceRoute servicePkg
  obtain ⟨vUnary, rUnary, nUnary, mUnary, qUnary, hUnary, _tUnary, pUnary, _cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg, _localPkg⟩ :=
      carrier
  have vPrimeUnary : UnaryHistory V' := unary_transport vUnary sameV
  have rPrimeUnary : UnaryHistory R' := unary_transport rUnary sameR
  have nPrimeUnary : UnaryHistory N' := unary_transport nUnary sameN
  have mPrimeUnary : UnaryHistory M' := unary_transport mUnary sameM
  have qPrimeUnary : UnaryHistory Q' := unary_transport qUnary sameQ
  have serviceUnary : UnaryHistory serviceRead :=
    unary_cont_closed qUnary hUnary serviceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row serviceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V' ∨ hsame row R' ∨ hsame row N' ∨ hsame row M' ∨
              hsame row Q' ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row serviceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q H serviceRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle serviceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro serviceRead ⟨hsame_refl serviceRead, serviceUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, serviceRoute, provenancePkg, servicePkg⟩
  }
  exact
    ⟨cert, vPrimeUnary, rPrimeUnary, nPrimeUnary, mPrimeUnary, qPrimeUnary,
      serviceUnary⟩

end BEDC.Derived.NormedSpaceUp
