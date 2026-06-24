import BEDC.Derived.MetaCICRedexFrontierUp.SNObstructionRetention

namespace BEDC.Derived.MetaCICRedexFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICRedexFrontierObstructionRetention [AskSetup] [PackageSetup]
    {B A L P O E H C G N obstructionRead betaRead retentionRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICRedexFrontierCarrier B A L P O E H C G N →
      Cont O E obstructionRead →
        Cont B E betaRead →
          Cont obstructionRead C retentionRead →
            Cont retentionRead G handoffRead →
              PkgSig bundle handoffRead pkg →
                UnaryHistory O ∧ UnaryHistory obstructionRead ∧ UnaryHistory retentionRead ∧
                  UnaryHistory handoffRead ∧ hsame H (append B O) ∧
                    List.Mem (metaCICRedexFrontierEncodeBHist O)
                      (metaCICRedexFrontierToEventFlow
                        (MetaCICRedexFrontierUp.mk B A L P O E H C G N)) ∧
                      Cont O E obstructionRead ∧ Cont obstructionRead C retentionRead ∧
                        Cont retentionRead G handoffRead ∧
                          PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: MetaCICRedexFrontierCarrier BHist BMark Cont ProbeBundle PkgSig
  intro carrier obstructionRoute _betaRoute retentionRoute handoffRoute handoffPkg
  obtain ⟨_bUnary, _aUnary, _lUnary, _pUnary, oUnary, eUnary, gUnary, boundarySame,
    carrierBetaRoute, _carrierArgRoute, _carrierProvenanceRoute⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed oUnary eUnary obstructionRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed _bUnary eUnary carrierBetaRoute
  have retentionUnary : UnaryHistory retentionRead :=
    unary_cont_closed obstructionUnary cUnary retentionRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed retentionUnary gUnary handoffRoute
  have obstructionListed :
      List.Mem (metaCICRedexFrontierEncodeBHist O)
        (metaCICRedexFrontierToEventFlow
          (MetaCICRedexFrontierUp.mk B A L P O E H C G N)) := by
    change
      List.Mem (metaCICRedexFrontierEncodeBHist O)
        [[BMark.b0], metaCICRedexFrontierEncodeBHist B, [BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist A, [BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist O,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist E,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          metaCICRedexFrontierEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist G,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist N]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))))
  exact
    ⟨oUnary, obstructionUnary, retentionUnary, handoffUnary, boundarySame,
      obstructionListed, obstructionRoute, retentionRoute, handoffRoute, handoffPkg⟩

end BEDC.Derived.MetaCICRedexFrontierUp
