import BEDC.Derived.BolzanoWeierstrassUp.RetainedCellMonotonicity
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_tail_cell_stability
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N earlierCell laterCell earlierWindow laterWindow nextLedger
      readback tailSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K earlierCell ->
        Cont earlierCell K laterCell ->
          Cont earlierCell S earlierWindow ->
            Cont laterCell S laterWindow ->
              Cont laterWindow R nextLedger ->
                Cont nextLedger Q readback ->
                  Cont readback E tailSeal ->
                    PkgSig bundle tailSeal pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row tailSeal ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row earlierCell ∨ hsame row laterCell ∨
                              hsame row laterWindow ∨ hsame row nextLedger ∨
                                hsame row readback ∨ hsame row tailSeal)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle tailSeal pkg)
                          hsame ∧
                        UnaryHistory laterCell ∧ UnaryHistory laterWindow ∧
                          UnaryHistory nextLedger ∧ UnaryHistory readback ∧
                            UnaryHistory tailSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier earlierRoute laterRoute _earlierWindowRoute laterWindowRoute ledgerRoute
    readbackRoute tailRoute tailPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have earlierUnary : UnaryHistory earlierCell :=
    unary_cont_closed SUnary KUnary earlierRoute
  have laterUnary : UnaryHistory laterCell :=
    unary_cont_closed earlierUnary KUnary laterRoute
  have laterWindowUnary : UnaryHistory laterWindow :=
    unary_cont_closed laterUnary SUnary laterWindowRoute
  have ledgerUnary : UnaryHistory nextLedger :=
    unary_cont_closed laterWindowUnary RUnary ledgerRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed ledgerUnary QUnary readbackRoute
  have tailUnary : UnaryHistory tailSeal :=
    unary_cont_closed readbackUnary EUnary tailRoute
  have sourceTail :
      (fun row : BHist => hsame row tailSeal ∧ UnaryHistory row) tailSeal := by
    exact ⟨hsame_refl tailSeal, tailUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row earlierCell ∨ hsame row laterCell ∨ hsame row laterWindow ∨
              hsame row nextLedger ∨ hsame row readback ∨ hsame row tailSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle tailSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailSeal sourceTail
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierPkg, tailPkg⟩
  }
  exact ⟨cert, laterUnary, laterWindowUnary, ledgerUnary, readbackUnary, tailUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
