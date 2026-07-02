import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive MetaCICParallelDiamondFrontierUp : Type where
  | mk :
      (premise peak join residual checker fragment bounded obstruction transport replay
        provenance localName : BHist) →
      MetaCICParallelDiamondFrontierUp

def MetacicParallelDiamondFrontierCarrier [AskSetup] [PackageSetup]
    (premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory premise ∧ UnaryHistory peak ∧ UnaryHistory join ∧
    UnaryHistory residual ∧ UnaryHistory checker ∧ UnaryHistory fragment ∧
      UnaryHistory bounded ∧ UnaryHistory obstruction ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg

theorem MetacicParallelDiamondFrontierObligations [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨premiseUnary, peakUnary, joinUnary, residualUnary, checkerUnary,
    fragmentUnary, boundedUnary, obstructionUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, provenancePkg⟩ := carrier
  have sourceWitness :
      (fun row : BHist =>
        (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
          hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
            hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
          UnaryHistory row) premise := by
    exact ⟨Or.inl (hsame_refl premise), premiseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro premise sourceWitness
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }
  exact ⟨cert, provenancePkg⟩

theorem MetacicParallelDiamondFrontierFiniteResidualWitnessConsumption [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName witnessRead closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg →
      Cont residual checker witnessRead →
        Cont witnessRead localName closedRead →
          PkgSig bundle closedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row closedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row premise ∨ hsame row peak ∨ hsame row join ∨
                    hsame row residual ∨ hsame row checker ∨ hsame row obstruction ∨
                      hsame row witnessRead ∨ hsame row closedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont residual checker witnessRead ∧
                    Cont witnessRead localName closedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle closedRead pkg)
                hsame ∧
              UnaryHistory witnessRead ∧ UnaryHistory closedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier residualChecker witnessLocal closedPkg
  obtain ⟨_premiseUnary, _peakUnary, _joinUnary, residualUnary, checkerUnary,
    _fragmentUnary, _boundedUnary, _obstructionUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, provenancePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed residualUnary checkerUnary residualChecker
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed witnessUnary localNameUnary witnessLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨ hsame row residual ∨
              hsame row checker ∨ hsame row obstruction ∨ hsame row witnessRead ∨
                hsame row closedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residual checker witnessRead ∧
              Cont witnessRead localName closedRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle closedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro closedRead
          ⟨hsame_refl closedRead, closedUnary⟩
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
        right
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, residualChecker, witnessLocal, provenancePkg, closedPkg⟩
    }
  exact ⟨cert, witnessUnary, closedUnary⟩

theorem MetacicParallelDiamondFrontierCandidateNormalizationScope [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName candidateRead normalizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg →
      Cont peak join candidateRead →
        Cont candidateRead obstruction normalizedRead →
          PkgSig bundle normalizedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row normalizedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row premise ∨ hsame row peak ∨ hsame row join ∨
                    hsame row residual ∨ hsame row obstruction ∨ hsame row candidateRead ∨
                      hsame row normalizedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont peak join candidateRead ∧
                    Cont candidateRead obstruction normalizedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle normalizedRead pkg)
                hsame ∧
              UnaryHistory candidateRead ∧ UnaryHistory normalizedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier peakJoin candidateObstruction normalizedPkg
  obtain ⟨_premiseUnary, peakUnary, joinUnary, _residualUnary, _checkerUnary,
    _fragmentUnary, _boundedUnary, obstructionUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed peakUnary joinUnary peakJoin
  have normalizedUnary : UnaryHistory normalizedRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalizedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨ hsame row residual ∨
              hsame row obstruction ∨ hsame row candidateRead ∨ hsame row normalizedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont peak join candidateRead ∧
              Cont candidateRead obstruction normalizedRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle normalizedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro normalizedRead
          ⟨hsame_refl normalizedRead, normalizedUnary⟩
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
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, peakJoin, candidateObstruction, provenancePkg, normalizedPkg⟩
    }
  exact ⟨cert, candidateUnary, normalizedUnary⟩

theorem MetacicParallelDiamondFrontierClosurestatusGuard [AskSetup] [PackageSetup]
    {premise critical candidate residual sn obstruction transport replay provenance name
      statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory premise -> UnaryHistory critical -> UnaryHistory candidate ->
      UnaryHistory residual -> UnaryHistory sn -> UnaryHistory obstruction ->
        UnaryHistory transport -> UnaryHistory replay -> UnaryHistory provenance ->
          UnaryHistory name -> Cont premise critical candidate -> Cont residual sn obstruction ->
            Cont transport replay statusRead -> PkgSig bundle provenance pkg ->
              PkgSig bundle statusRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row premise ∨ hsame row critical ∨ hsame row candidate ∨
                        hsame row residual ∨ hsame row sn ∨ hsame row obstruction ∨
                          hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                            hsame row name ∨ hsame row statusRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont premise critical candidate ∧
                        Cont residual sn obstruction ∧ Cont transport replay statusRead ∧
                          PkgSig bundle statusRead pkg)
                    hsame ∧
                  UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: MetaCICParallelDiamondFrontier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _premiseUnary _criticalUnary _candidateUnary _residualUnary _snUnary _obstructionUnary
    transportUnary replayUnary _provenanceUnary _nameUnary premiseRoute residualRoute statusRoute
    _provenancePkg statusPkg
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed transportUnary replayUnary statusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row critical ∨ hsame row candidate ∨
              hsame row residual ∨ hsame row sn ∨ hsame row obstruction ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row statusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont premise critical candidate ∧
              Cont residual sn obstruction ∧ Cont transport replay statusRead ∧
                PkgSig bundle statusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro statusRead ⟨hsame_refl statusRead, statusUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
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
      right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, premiseRoute, residualRoute, statusRoute, statusPkg⟩
  }
  exact ⟨cert, statusUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
