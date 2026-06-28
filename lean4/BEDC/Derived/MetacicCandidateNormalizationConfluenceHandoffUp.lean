import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive MetacicCandidateNormalizationConfluenceHandoffUp : Type where
  | mk (A K N F C D B H R P L : BHist) :
      MetacicCandidateNormalizationConfluenceHandoffUp
  deriving DecidableEq

def MetacicCandidateNormalizationConfluenceHandoffCarrier [AskSetup] [PackageSetup]
    (audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory audit ∧
    UnaryHistory candidate ∧
      UnaryHistory normalEndpoint ∧
        UnaryHistory frontier ∧
          UnaryHistory confluence ∧
            UnaryHistory decidability ∧
              UnaryHistory blocked ∧
                UnaryHistory transport ∧
                  UnaryHistory replay ∧
                    UnaryHistory provenance ∧ UnaryHistory localName ∧
                      PkgSig bundle provenance pkg

theorem MetacicCandidateNormalizationConfluenceHandoffBoundary [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName consumerRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont audit candidate consumerRead →
        Cont consumerRead frontier frontierRead →
          PkgSig bundle frontierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
                    hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                      hsame row blocked ∨ hsame row frontierRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
                hsame ∧
              UnaryHistory consumerRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute consumerFrontierRoute frontierPkg
  have auditUnary : UnaryHistory audit := carrier.left
  have candidateUnary : UnaryHistory candidate := carrier.right.left
  have frontierUnary : UnaryHistory frontier := carrier.right.right.right.left
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed consumerUnary frontierUnary consumerFrontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
              hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                hsame row blocked ∨ hsame row frontierRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨frontierRead, hsame_refl frontierRead, frontierReadUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro row other same
      exact hsame_symm same
    · intro row middle other leftSame rightSame
      exact hsame_trans leftSame rightSame
    · intro row other same source
      exact
        ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    · intro row source
      exact ⟨source.right, frontierPkg⟩
  exact ⟨cert, consumerUnary, frontierReadUnary⟩

theorem MetacicCandidateNormalizationConfluenceHandoffObligationRows [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName consumerRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont audit candidate consumerRead →
        Cont consumerRead frontier frontierRead →
          PkgSig bundle frontierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
                    hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                      hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨ hsame row frontierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                    Cont audit candidate consumerRead ∧ Cont consumerRead frontier frontierRead)
                hsame ∧ UnaryHistory consumerRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute consumerFrontierRoute frontierPkg
  have auditUnary : UnaryHistory audit := carrier.left
  have candidateUnary : UnaryHistory candidate := carrier.right.left
  have frontierUnary : UnaryHistory frontier := carrier.right.right.right.left
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed consumerUnary frontierUnary consumerFrontierRoute
  refine ⟨?_, consumerUnary, frontierReadUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨frontierRead, hsame_refl frontierRead, frontierReadUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
      unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr sourceRow.left))))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, frontierPkg, auditCandidateRoute, consumerFrontierRoute⟩

theorem MetacicCandidateNormalizationConfluenceBoundary [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName confluenceRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont candidate confluence confluenceRead →
        Cont confluenceRead blocked boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidate ∨ hsame row frontier ∨ hsame row confluence ∨
                    hsame row decidability ∨ hsame row blocked ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                        hsame row confluenceRead ∨ hsame row boundaryRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont candidate confluence confluenceRead ∧
                    Cont confluenceRead blocked boundaryRead ∧
                      PkgSig bundle boundaryRead pkg)
                hsame ∧ UnaryHistory confluenceRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier confluenceRoute boundaryRoute boundaryPkg
  obtain ⟨_auditUnary, candidateUnary, _normalEndpointUnary, _frontierUnary,
    confluenceUnary, _decidabilityUnary, blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary confluenceUnary confluenceRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed confluenceReadUnary blockedUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row frontier ∨ hsame row confluence ∨
              hsame row decidability ∨ hsame row blocked ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row confluenceRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate confluence confluenceRead ∧
              Cont confluenceRead blocked boundaryRead ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, confluenceRoute, boundaryRoute, boundaryPkg⟩
  }
  exact ⟨cert, confluenceReadUnary, boundaryReadUnary⟩

end BEDC.Derived
