import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionTailDigitStability [AskSetup] [PackageSetup]
    {D W V Q R E H C P N tailRead comparison handoff sealRead transportedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory H ->
                Cont D W tailRead ->
                  Cont tailRead V comparison ->
                    Cont comparison Q handoff ->
                      Cont handoff R sealRead ->
                        hsame transportedTail tailRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle transportedTail pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row transportedTail ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row D ∨ hsame row W ∨ hsame row tailRead ∨
                                      hsame row transportedTail)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle transportedTail pkg ∧
                                      PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory transportedTail ∧ UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary _hUnary digitWindow tailPlace comparisonDyadic
    handoffRegular sameTransportedTail provenancePkg transportedTailPkg
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed dUnary wUnary digitWindow
  have _comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed tailReadUnary vUnary tailPlace
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed _comparisonUnary qUnary comparisonDyadic
  have _sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary rUnary handoffRegular
  have transportedTailUnary : UnaryHistory transportedTail :=
    unary_transport_symm tailReadUnary sameTransportedTail
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedTail ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row tailRead ∨ hsame row transportedTail)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle transportedTail pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedTail
          ⟨hsame_refl transportedTail, transportedTailUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportedTailPkg, provenancePkg⟩
  }
  exact ⟨cert, transportedTailUnary, tailReadUnary⟩

end BEDC.Derived.DecimalExpansionUp
