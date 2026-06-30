import BEDC.Derived.ToeplitzLemmaUp.RegularSequenceHandoff

namespace BEDC.Derived.ToeplitzLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ToeplitzLemmaNamecertObligations [AskSetup] [PackageSetup]
    {A W R D T E H C P N matrixRead readbackRead transformedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToeplitzLemmaCarrier A W R D T E H C P N bundle pkg →
      Cont A W matrixRead →
        Cont matrixRead R readbackRead →
          Cont D readbackRead transformedRead →
            Cont transformedRead E sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                        hsame row T ∨ hsame row E ∨ hsame row matrixRead ∨
                          hsame row readbackRead ∨ hsame row transformedRead ∨
                            hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A W matrixRead ∧
                        Cont matrixRead R readbackRead ∧
                          Cont D readbackRead transformedRead ∧
                            Cont transformedRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg)
                    hsame ∧ UnaryHistory matrixRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory transformedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier matrixRoute readbackRoute transformedRoute sealRoute sealPkg
  obtain ⟨aUnary, wUnary, rUnary, dUnary, _tUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, provenancePkg, _namePkg⟩ := carrier
  have matrixUnary : UnaryHistory matrixRead :=
    unary_cont_closed aUnary wUnary matrixRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed matrixUnary rUnary readbackRoute
  have transformedUnary : UnaryHistory transformedRead :=
    unary_cont_closed dUnary readbackUnary transformedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed transformedUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
              hsame row E ∨ hsame row matrixRead ∨ hsame row readbackRead ∨
                hsame row transformedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W matrixRead ∧ Cont matrixRead R readbackRead ∧
              Cont D readbackRead transformedRead ∧ Cont transformedRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, matrixRoute, readbackRoute, transformedRoute, sealRoute,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, matrixUnary, readbackUnary, transformedUnary, sealUnary⟩

end BEDC.Derived.ToeplitzLemmaUp
