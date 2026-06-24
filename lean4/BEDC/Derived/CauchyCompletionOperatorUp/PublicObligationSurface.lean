import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorPublicObligationSurface [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg ->
      Cont M U boundaryRead ->
        Cont B S finiteWindow ->
          Cont D Q separatedRead ->
            Cont separatedRead E sealRead ->
              Cont sealRead N publicRead ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row B ∨ hsame row U ∨ hsame row S ∨
                        hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M U boundaryRead ∧
                        Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
                          Cont separatedRead E sealRead ∧ Cont sealRead N publicRead ∧
                            PkgSig bundle publicRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet boundaryRoute finiteRoute separatedRoute sealRoute publicRoute publicPkg
  obtain ⟨mUnary, bUnary, uUnary, sUnary, _rUnary, dUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary uUnary boundaryRoute
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed bUnary sUnary finiteRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed dUnary qUnary separatedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nUnary publicRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                            (Or.inr
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, boundaryRoute, finiteRoute, separatedRoute, sealRoute,
          publicRoute, publicPkg⟩
  }

end BEDC.Derived.CauchyCompletionOperatorUp
