import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathParallelDiamondFrontierHandoffScope [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName diamondLeft diamondRight retainedFrontier consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route handoff diamondLeft ->
        Cont route dischargeSocket diamondRight ->
          Cont diamondLeft diamondRight retainedFrontier ->
            Cont retainedFrontier localName consumerRead ->
              PkgSig bundle retainedFrontier pkg ->
                PkgSig bundle consumerRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row diamondLeft ∨ hsame row diamondRight ∨
                          hsame row retainedFrontier ∨ hsame row consumerRead ∨
                            hsame row route ∨ hsame row handoff ∨ hsame row dischargeSocket)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont route handoff diamondLeft ∧
                          Cont route dischargeSocket diamondRight ∧
                            Cont diamondLeft diamondRight retainedFrontier ∧
                              Cont retainedFrontier localName consumerRead ∧
                                PkgSig bundle retainedFrontier pkg ∧
                                  PkgSig bundle consumerRead pkg)
                      hsame ∧
                    UnaryHistory diamondLeft ∧ UnaryHistory diamondRight ∧
                      UnaryHistory retainedFrontier ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeHandoffLeft routeSocketRight leftRightFrontier frontierLocalConsumer
    frontierPkg consumerPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have diamondLeftUnary : UnaryHistory diamondLeft :=
    unary_cont_closed routeUnary handoffUnary routeHandoffLeft
  have diamondRightUnary : UnaryHistory diamondRight :=
    unary_cont_closed routeUnary dischargeSocketUnary routeSocketRight
  have retainedFrontierUnary : UnaryHistory retainedFrontier :=
    unary_cont_closed diamondLeftUnary diamondRightUnary leftRightFrontier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed retainedFrontierUnary localNameUnary frontierLocalConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diamondLeft ∨ hsame row diamondRight ∨
              hsame row retainedFrontier ∨ hsame row consumerRead ∨ hsame row route ∨
                hsame row handoff ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route handoff diamondLeft ∧
              Cont route dischargeSocket diamondRight ∧
                Cont diamondLeft diamondRight retainedFrontier ∧
                  Cont retainedFrontier localName consumerRead ∧
                    PkgSig bundle retainedFrontier pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeHandoffLeft, routeSocketRight, leftRightFrontier,
          frontierLocalConsumer, frontierPkg, consumerPkg⟩
  }
  exact
    ⟨cert, diamondLeftUnary, diamondRightUnary, retainedFrontierUnary, consumerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
