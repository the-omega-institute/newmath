import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchReadback

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_obligation_branch_readback [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback exportRead →
            PkgSig bundle exportRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                      hsame row readback ∨ hsame row exportRead)
                  (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                  UnaryHistory readback ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute exportRoute exportPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed branchReadUnary readbackUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readback ∨ hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportPkg⟩
    }
  exact ⟨cert, selectedUnary, branchReadUnary, readbackUnary, exportUnary⟩

theorem MetricCompletion_obligation_uniform_handoff [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead uniformConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead replay uniformConsumer →
            PkgSig bundle uniformConsumer pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row uniformConsumer ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                      hsame row readback ∨ hsame row separated ∨ hsame row replay ∨
                        hsame row uniformConsumer)
                  (fun row : BHist => hsame row uniformConsumer ∧
                    PkgSig bundle uniformConsumer pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory selectedBranch ∧
                  UnaryHistory branchRead ∧ UnaryHistory readback ∧ UnaryHistory separated ∧
                    UnaryHistory replay ∧ UnaryHistory uniformConsumer ∧
                      Cont readback separated replay ∧
                        Cont branchRead replay uniformConsumer := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute uniformRoute uniformPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have uniformUnary : UnaryHistory uniformConsumer :=
    unary_cont_closed branchReadUnary replayUnary uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformConsumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readback ∨ hsame row separated ∨ hsame row replay ∨
                hsame row uniformConsumer)
          (fun row : BHist => hsame row uniformConsumer ∧
            PkgSig bundle uniformConsumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformConsumer ⟨hsame_refl uniformConsumer,
          uniformUnary⟩
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
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, uniformPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, readbackUnary, separatedUnary,
      replayUnary, uniformUnary, replayRoute, uniformRoute⟩

theorem MetricCompletion_branch_conversion_refusal [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      filterRead netRead mixedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg ->
      Cont filterBranch readback filterRead ->
        Cont netBranch readback netRead ->
          Cont filterRead netRead mixedRead ->
            PkgSig bundle mixedRead pkg ->
              UnaryHistory filterBranch ∧ UnaryHistory netBranch ∧ UnaryHistory filterRead ∧
                UnaryHistory netRead ∧ UnaryHistory mixedRead ∧
                  Cont filterBranch readback filterRead ∧ Cont netBranch readback netRead ∧
                    Cont filterRead netRead mixedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle mixedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier filterRoute netRoute mixedRoute mixedPkg
  obtain ⟨_sourceUnary, filterUnary, netUnary, readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed filterUnary readbackUnary filterRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed netUnary readbackUnary netRoute
  have mixedReadUnary : UnaryHistory mixedRead :=
    unary_cont_closed filterReadUnary netReadUnary mixedRoute
  exact
    ⟨filterUnary, netUnary, filterReadUnary, netReadUnary, mixedReadUnary, filterRoute,
      netRoute, mixedRoute, provenancePkg, mixedPkg⟩

theorem MetricCompletion_obligation_separated_comparison [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead separatedRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead separated separatedRead →
            Cont separatedRead transport comparisonRead →
              PkgSig bundle comparisonRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                        hsame row separated ∨ hsame row comparisonRead)
                    (fun row : BHist =>
                      hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory selectedBranch ∧
                    UnaryHistory branchRead ∧ UnaryHistory separated ∧
                      UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute separatedRoute comparisonRoute comparisonPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, _readbackUnary, separatedUnary,
    transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _carrierReplay,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed branchReadUnary separatedUnary separatedRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed separatedReadUnary transportUnary comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row separated ∨ hsame row comparisonRead)
          (fun row : BHist => hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro comparisonRead
          ⟨hsame_refl comparisonRead, comparisonUnary⟩
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
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, comparisonPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, separatedUnary, comparisonUnary⟩

end BEDC.Derived.MetricCompletionUp.BranchReadback

namespace BEDC.Derived.MetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_source_branch_readback [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead toleranceRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback toleranceRead →
            Cont toleranceRead separated sealedRead →
              PkgSig bundle sealedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                        hsame row toleranceRead ∨ hsame row separated ∨ hsame row sealedRead)
                    (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealedRead ∧
                      Cont source selectedBranch branchRead ∧
                        Cont branchRead readback toleranceRead ∧
                          Cont toleranceRead separated sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute toleranceRoute sealedRoute sealedPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _carrierReplay,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed branchReadUnary readbackUnary toleranceRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed toleranceUnary separatedUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row toleranceRead ∨ hsame row separated ∨ hsame row sealedRead)
          (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, sealedPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, toleranceUnary, sealedUnary,
      branchRoute, toleranceRoute, sealedRoute⟩

end BEDC.Derived.MetricCompletionUp
