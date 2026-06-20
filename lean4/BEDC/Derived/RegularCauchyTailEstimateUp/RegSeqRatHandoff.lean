import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {M W D R E H C P N toleranceRead windowRead readbackRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      Cont D W toleranceRead ->
        Cont toleranceRead R windowRead ->
          Cont windowRead E readbackRead ->
            Cont readbackRead C handoffRead ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D W toleranceRead ∧
                        Cont toleranceRead R windowRead ∧ Cont windowRead E readbackRead ∧
                          Cont readbackRead C handoffRead ∧ PkgSig bundle handoffRead pkg)
                    hsame ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier toleranceWindow windowReadback readbackSeal replayHandoff handoffPkg
  obtain ⟨_unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryD unaryW toleranceWindow
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary unaryR windowReadback
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryE readbackSeal
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed readbackUnary unaryC replayHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W toleranceRead ∧
              Cont toleranceRead R windowRead ∧ Cont windowRead E readbackRead ∧
                Cont readbackRead C handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, toleranceWindow, windowReadback, readbackSeal, replayHandoff,
          handoffPkg⟩
  }
  exact ⟨cert, toleranceUnary, windowUnary, readbackUnary, handoffUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
