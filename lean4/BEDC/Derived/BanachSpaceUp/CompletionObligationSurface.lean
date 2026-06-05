import BEDC.Derived.BanachSpaceUp.CompletionConsumerScope
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCompletionObligationSurface [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L completionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg) →
      Cont Q S completionRead →
        Cont completionRead E namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
                  hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row Z ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                      hsame row completionRead ∨ hsame row namedRead)
              (fun row : BHist => PkgSig bundle row pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame SemanticNameCert
  intro packet completionRoute namedRoute namedPkg
  obtain ⟨_vUnary, _nUnary, _mUnary, qUnary, sUnary, _rUnary, eUnary, _zUnary,
    _hUnary, _cUnary, _pUnary, _lUnary, _pkgP⟩ := packet
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed qUnary sUnary completionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed completionUnary eUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
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
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact namedPkg
  }

end BEDC.Derived.BanachSpaceUp
