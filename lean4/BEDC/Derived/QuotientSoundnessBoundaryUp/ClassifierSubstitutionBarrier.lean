import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_classifier_substitution_barrier
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      hsame classifierRead e →
        Cont v t refusalRead →
          Cont t h transportRead →
            PkgSig bundle transportRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                    hsame classifierRead e ∧ Cont v t refusalRead ∧
                      Cont t h transportRead ∧ hsame row transportRead)
                (fun row : BHist =>
                  hsame classifierRead e ∧ Cont e t h ∧ Cont t h row)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle transportRead pkg ∧ hsame h n)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier classifierSame vTRefusal tHTransport transportPkg
  have sourceWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
        hsame classifierRead e ∧ Cont v t refusalRead ∧
          Cont t h transportRead ∧ hsame transportRead transportRead :=
    ⟨carrier, classifierSame, vTRefusal, tHTransport, hsame_refl transportRead⟩
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  exact {
    core := {
      carrier_inhabited := Exists.intro transportRead sourceWitness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            source.right.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.right.left, eTH,
          cont_result_hsame_transport source.right.right.right.left
            (hsame_symm source.right.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport transportUnary (hsame_symm source.right.right.right.right),
          transportPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
