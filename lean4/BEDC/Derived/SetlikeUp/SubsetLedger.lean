import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeSubsetLedger_exactness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N subsetReplay comprehensionReplay ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory I ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont Q I subsetReplay ->
                Cont R E comprehensionReplay ->
                  Cont subsetReplay comprehensionReplay ledgerRead ->
                    PkgSig bundle P pkg ->
                      UnaryHistory subsetReplay ∧ UnaryHistory comprehensionReplay ∧
                        UnaryHistory ledgerRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
                                Cont Q I subsetReplay ∨ Cont R E comprehensionReplay)
                            (fun row : BHist => PkgSig bundle P pkg ∧ hsame row ledgerRead)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields rowsQ rowsI rowsR rowsE subsetRoute comprehensionRoute ledgerRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subsetUnary comprehensionUnary ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
            Cont Q I subsetReplay ∨ Cont R E comprehensionReplay)
        (fun row : BHist => PkgSig bundle P pkg ∧ hsame row ledgerRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl subsetRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨packageRead, source.left⟩
  }
  exact ⟨subsetUnary, comprehensionUnary, ledgerUnary, cert⟩

end BEDC.Derived.SetlikeUp
