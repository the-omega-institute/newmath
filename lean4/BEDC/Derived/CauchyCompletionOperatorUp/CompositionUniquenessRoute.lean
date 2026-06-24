import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorCompositionUniquenessRoute [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead route0
      route1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg →
      Cont M U boundaryRead →
        Cont B S finiteWindow →
          Cont D Q separatedRead →
            Cont separatedRead E sealRead →
              Cont sealRead N route0 →
                Cont sealRead N route1 →
                  PkgSig bundle route0 pkg →
                    PkgSig bundle route1 pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row route0 ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
                              hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                  hsame row route0)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M U boundaryRead ∧
                              Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
                                Cont separatedRead E sealRead ∧ Cont sealRead N route0 ∧
                                  PkgSig bundle route0 pkg)
                          hsame ∧
                        hsame route0 route1 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro packet boundaryRoute windowRoute separatedRoute sealRoute route0Route route1Route
    route0Pkg _route1Pkg
  obtain ⟨mUnary, bUnary, uUnary, sUnary, _rUnary, dUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed bUnary sUnary windowRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed dUnary qUnary separatedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedUnary eUnary sealRoute
  have route0Unary : UnaryHistory route0 :=
    unary_cont_closed sealUnary nUnary route0Route
  have routeAgreement : hsame route0 route1 :=
    cont_deterministic route0Route route1Route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route0 ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨ hsame row R ∨
              hsame row D ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row route0)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M U boundaryRead ∧ Cont B S finiteWindow ∧
              Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
                Cont sealRead N route0 ∧ PkgSig bundle route0 pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route0 ⟨hsame_refl route0, route0Unary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, windowRoute, separatedRoute, sealRoute,
          route0Route, route0Pkg⟩
  }
  exact ⟨cert, routeAgreement⟩

end BEDC.Derived.CauchyCompletionOperatorUp
