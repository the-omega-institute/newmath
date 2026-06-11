import BEDC.Derived.MetaCICClosureTraceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_public_bridge_obligation [AskSetup] [PackageSetup]
    {S U V B R G K H C P N publicRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg →
      Cont (append (append S U) G) (append B R) publicRead →
        Cont publicRead N bridgeRead →
          PkgSig bundle bridgeRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ∧
                    hsame row bridgeRead)
                (fun row : BHist =>
                  hsame row (append (append S U) G) ∨ hsame row (append B R) ∨
                    hsame row K ∨ hsame row N ∨ hsame row publicRead ∨
                      hsame row bridgeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    Cont (append (append S U) G) (append B R) publicRead ∧
                      Cont publicRead N bridgeRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle bridgeRead pkg)
                hsame ∧ UnaryHistory publicRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute bridgeRoute bridgePkg
  have carrierSource :
      MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg :=
    carrier
  obtain ⟨SUnary, UUnary, _VUnary, BUnary, RUnary, GUnary, _KUnary, _HUnary,
    _CUnary, _PUnary, NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
    provenancePkg⟩ := carrier
  have SUUnary : UnaryHistory (append S U) :=
    unary_append_closed SUnary UUnary
  have generatorUnary : UnaryHistory (append (append S U) G) :=
    unary_append_closed SUUnary GUnary
  have betaUnary : UnaryHistory (append B R) :=
    unary_append_closed BUnary RUnary
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed generatorUnary betaUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary NUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ∧
              hsame row bridgeRead)
          (fun row : BHist =>
            hsame row (append (append S U) G) ∨ hsame row (append B R) ∨
              hsame row K ∨ hsame row N ∨ hsame row publicRead ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont (append (append S U) G) (append B R) publicRead ∧
              Cont publicRead N bridgeRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨carrierSource, hsame_refl bridgeRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport bridgeUnary (hsame_symm source.right), publicRoute,
          bridgeRoute, provenancePkg, bridgePkg⟩
  }
  exact ⟨cert, publicUnary, bridgeUnary⟩

end BEDC.Derived.MetaCICClosureTraceUp
