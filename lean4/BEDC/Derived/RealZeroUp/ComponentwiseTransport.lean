import BEDC.Derived.RealZeroUp

namespace BEDC.Derived.RealZeroUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RealZeroComponentwiseTransport
    {q S Z0 D R H C P N q' S' Z0' D' R' H' C' P' N' read read' : BHist} :
    RealZeroCarrier q S Z0 D R H C P N →
      RealZeroCarrier q' S' Z0' D' R' H' C' P' N' →
        hsame R' R →
          hsame N' N →
            Cont R N read →
              Cont R' N' read' →
                SemanticNameCert
                    (fun row : BHist => hsame row read' ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row q' ∨ hsame row S' ∨ hsame row Z0' ∨ hsame row D' ∨
                        hsame row R' ∨ hsame row H' ∨ hsame row C' ∨ hsame row P' ∨
                          hsame row N' ∨ hsame row read')
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont q' S' Z0' ∧ Cont Z0' D' R' ∧
                        Cont R' N' read')
                    hsame ∧
                  hsame read' read ∧ UnaryHistory read' := by
  -- BEDC touchpoint anchor: RealZeroCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro _carrier carrier' sameR sameN readRoute readRoute'
  obtain ⟨_qUnary', _sUnary', _z0Unary', _dUnary', rUnary', _hUnary', _cUnary',
    _pUnary', nUnary', zeroRoute', terminalRoute', _sameH', _sameC', _sameP',
    _sameN', _terminalCert'⟩ := carrier'
  have readUnary' : UnaryHistory read' :=
    unary_cont_closed rUnary' nUnary' readRoute'
  have sameRead : hsame read' read :=
    cont_respects_hsame sameR sameN readRoute' readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read' ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q' ∨ hsame row S' ∨ hsame row Z0' ∨ hsame row D' ∨
              hsame row R' ∨ hsame row H' ∨ hsame row C' ∨ hsame row P' ∨
                hsame row N' ∨ hsame row read')
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q' S' Z0' ∧ Cont Z0' D' R' ∧ Cont R' N' read')
          hsame := {
    core := {
      carrier_inhabited := Exists.intro read' ⟨hsame_refl read', readUnary'⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zeroRoute', terminalRoute', readRoute'⟩
  }
  exact ⟨cert, sameRead, readUnary'⟩

end BEDC.Derived.RealZeroUp
