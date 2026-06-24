import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorObligationTriad [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg →
      Cont M U boundaryRead →
        Cont B S finiteWindow →
          Cont D Q separatedRead →
            Cont separatedRead E sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row S ∨ hsame row D ∨ hsame row Q ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row finiteWindow ∨
                            hsame row separatedRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B S finiteWindow ∧
                        Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory finiteWindow ∧ UnaryHistory separatedRead ∧
                    UnaryHistory sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet _boundaryRoute windowRoute separatedRoute sealRoute sealPkg
  obtain ⟨_mUnary, bUnary, _uUnary, sUnary, _rUnary, dUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed bUnary sUnary windowRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed dUnary qUnary separatedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row D ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row finiteWindow ∨ hsame row separatedRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
              Cont separatedRead E sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, windowRoute, separatedRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, finiteUnary, separatedUnary, sealUnary, sealPkg⟩

end BEDC.Derived.CauchyCompletionOperatorUp
