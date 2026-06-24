import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffParallelFrontierConsumption
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName publicRead frontierRead confluenceRead decidableRead blockerRead
      rectangleRead joinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont audit candidate publicRead ->
        Cont publicRead frontier frontierRead ->
          Cont frontierRead confluence confluenceRead ->
            Cont confluenceRead decidability decidableRead ->
              Cont confluenceRead blocked blockerRead ->
                Cont decidableRead blockerRead rectangleRead ->
                  Cont rectangleRead blocked joinRead ->
                    PkgSig bundle rectangleRead pkg ->
                      PkgSig bundle joinRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row joinRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row candidate ∨ hsame row frontier ∨
                                hsame row confluence ∨ hsame row decidability ∨
                                  hsame row blocked ∨ hsame row rectangleRead ∨
                                    hsame row joinRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                Cont frontierRead confluence confluenceRead ∧
                                  Cont confluenceRead decidability decidableRead ∧
                                    Cont confluenceRead blocked blockerRead ∧
                                      Cont decidableRead blockerRead rectangleRead ∧
                                        Cont rectangleRead blocked joinRead ∧
                                          PkgSig bundle joinRead pkg)
                            hsame ∧
                          UnaryHistory frontierRead ∧ UnaryHistory confluenceRead ∧
                            UnaryHistory decidableRead ∧ UnaryHistory blockerRead ∧
                              UnaryHistory rectangleRead ∧ UnaryHistory joinRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditCandidateRoute publicFrontierRoute frontierConfluenceRoute
    confluenceDecidableRoute confluenceBlockedRoute rectangleRoute joinRoute _rectanglePkg
    joinPkg
  obtain ⟨auditUnary, candidateUnary, _normalUnary, frontierUnary, confluenceUnary,
    decidabilityUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed publicUnary frontierUnary publicFrontierRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed frontierReadUnary confluenceUnary frontierConfluenceRoute
  have decidableReadUnary : UnaryHistory decidableRead :=
    unary_cont_closed confluenceReadUnary decidabilityUnary confluenceDecidableRoute
  have blockerReadUnary : UnaryHistory blockerRead :=
    unary_cont_closed confluenceReadUnary blockedUnary confluenceBlockedRoute
  have rectangleReadUnary : UnaryHistory rectangleRead :=
    unary_cont_closed decidableReadUnary blockerReadUnary rectangleRoute
  have joinReadUnary : UnaryHistory joinRead :=
    unary_cont_closed rectangleReadUnary blockedUnary joinRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joinRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row frontier ∨ hsame row confluence ∨
              hsame row decidability ∨ hsame row blocked ∨ hsame row rectangleRead ∨
                hsame row joinRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontierRead confluence confluenceRead ∧
              Cont confluenceRead decidability decidableRead ∧
                Cont confluenceRead blocked blockerRead ∧
                  Cont decidableRead blockerRead rectangleRead ∧
                    Cont rectangleRead blocked joinRead ∧ PkgSig bundle joinRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joinRead ⟨hsame_refl joinRead, joinReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, frontierConfluenceRoute, confluenceDecidableRoute,
          confluenceBlockedRoute, rectangleRoute, joinRoute, joinPkg⟩
  }
  exact
    ⟨cert, frontierReadUnary, confluenceReadUnary, decidableReadUnary, blockerReadUnary,
      rectangleReadUnary, joinReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
