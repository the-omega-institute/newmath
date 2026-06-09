import BEDC.Derived.DyadicIntervalCoverUp.BridgeExport
import BEDC.Derived.DyadicIntervalCoverUp.FiniteCoverBridgeScope

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverUniformModulusBridgeConsumer [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N bridge uniform : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont V W bridge →
        Cont bridge R uniform →
          PkgSig bundle uniform pkg →
            SemanticNameCert
                (fun row : BHist => hsame row uniform ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                    hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                      hsame row bridge ∨ hsame row uniform)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont V W bridge ∧ Cont bridge R uniform ∧
                    PkgSig bundle uniform pkg)
                hsame ∧
              UnaryHistory bridge ∧ UnaryHistory uniform := by
  -- BEDC touchpoint anchor: DyadicIntervalCoverRootObligationSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface vwBridge bridgeRUniform uniformPkg
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed vUnary wUnary vwBridge
  have uniformUnary : UnaryHistory uniform :=
    unary_cont_closed bridgeUnary rUnary bridgeRUniform
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniform ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row bridge ∨
                hsame row uniform)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V W bridge ∧ Cont bridge R uniform ∧
              PkgSig bundle uniform pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniform ⟨hsame_refl uniform, uniformUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceData.left))))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, vwBridge, bridgeRUniform, uniformPkg⟩
  }
  exact ⟨cert, bridgeUnary, uniformUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
