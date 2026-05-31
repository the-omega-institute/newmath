import BEDC.Derived.RealityConstrainedTruthCertUp

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem RealityConstrainedTruthCert_scoped_tastegate_route [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N openFit objectivity explanation induction tower
      exportRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N ->
      Cont S K openFit ->
        Cont I L objectivity ->
          Cont Sigma K explanation ->
            Cont T U induction ->
              Cont D L tower ->
                Cont N tower exportRead ->
                  PkgSig bundle exportRead pkg ->
                    Nonempty (ChapterTasteGate TasteGate.RealityConstrainedTruthCertUp) ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row openFit ∨ hsame row objectivity ∨
                            hsame row explanation ∨ hsame row induction ∨
                              hsame row tower ∨ hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                        hsame ∧
                      UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier openFitRoute objectivityRoute explanationRoute inductionRoute towerRoute
    exportRoute exportPkg
  have handoff :=
    RealityConstrainedTruthCertSiblingHandoffTotality carrier openFitRoute objectivityRoute
      explanationRoute inductionRoute towerRoute exportRoute exportPkg
  exact
    ⟨⟨inferInstance⟩, handoff.left,
      handoff.right.right.right.right.right.right⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
