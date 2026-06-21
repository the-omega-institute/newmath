import BEDC.Derived.EpigraphUp

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EpigraphLedgerExactness [AskSetup] [PackageSetup]
    {D V L O H C P N lowerRead transportedRead replayRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphContPkgCarrier D V L O H C P N bundle pkg ->
      Cont L O lowerRead ->
        Cont lowerRead H transportedRead ->
          Cont transportedRead C replayRead ->
            Cont replayRead P ledgerRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row lowerRead ∨ hsame row transportedRead ∨
                              hsame row replayRead ∨ hsame row ledgerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L O lowerRead ∧
                          Cont lowerRead H transportedRead ∧
                            Cont transportedRead C replayRead ∧
                              Cont replayRead P ledgerRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory lowerRead ∧ UnaryHistory transportedRead ∧
                    UnaryHistory replayRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier lowerRoute transportRoute replayRoute ledgerRoute provenancePkg namePkg
  obtain ⟨_dUnary, _vUnary, lUnary, oUnary, hUnary, cUnary, pUnary, _nUnary,
    _carrierValueRoute, _carrierTransportRoute, _carrierProvenancePkg,
      _carrierNamePkg⟩ := carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed lUnary oUnary lowerRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed lowerUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed replayUnary pUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
                hsame row transportedRead ∨ hsame row replayRead ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L O lowerRead ∧ Cont lowerRead H transportedRead ∧
              Cont transportedRead C replayRead ∧ Cont replayRead P ledgerRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, transportRoute, replayRoute, ledgerRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, lowerUnary, transportedUnary, replayUnary, ledgerUnary⟩

end BEDC.Derived.EpigraphUp
