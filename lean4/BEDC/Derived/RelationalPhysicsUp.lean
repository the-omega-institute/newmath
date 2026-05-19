import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RelationalPhysicsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RelationalPhysicsCarrier [AskSetup] [PackageSetup]
    (observer invariant locality audit rate transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory observer ∧ UnaryHistory invariant ∧ UnaryHistory locality ∧
    UnaryHistory audit ∧ UnaryHistory rate ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont locality invariant audit ∧
        Cont audit rate route ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem RelationalPhysics_namecert_handoff [AskSetup] [PackageSetup]
    {observer invariant locality audit rate transport route provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalPhysicsCarrier observer invariant locality audit rate transport route provenance
        name bundle pkg →
      Cont locality invariant audit →
        Cont audit rate handoff →
          PkgSig bundle handoff pkg →
            UnaryHistory observer ∧ UnaryHistory locality ∧ UnaryHistory invariant ∧
              UnaryHistory audit ∧ UnaryHistory rate ∧ UnaryHistory handoff ∧
                Cont locality invariant audit ∧ Cont audit rate handoff ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier localityInvariantAudit auditRateHandoff handoffPkg
  obtain ⟨observerUnary, invariantUnary, localityUnary, auditUnary, rateUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _carrierLocalityInvariantAudit, _carrierAuditRateRoute, provenancePkg, _namePkg⟩ :=
    carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditUnary rateUnary auditRateHandoff
  exact
    ⟨observerUnary, localityUnary, invariantUnary, auditUnary, rateUnary, handoffUnary,
      localityInvariantAudit, auditRateHandoff, provenancePkg, handoffPkg⟩

theorem RelationalPhysicsCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observer invariant locality audit rateOrRefusal transport continuation provenance
      name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalPhysicsCarrier observer invariant locality audit rateOrRefusal transport
        continuation provenance name bundle pkg ->
      Cont observer locality invariant ->
        Cont invariant audit handoff ->
          PkgSig bundle handoff pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row observer ∨ hsame row locality ∨ hsame row invariant ∨
                    hsame row audit ∨ hsame row rateOrRefusal ∨ hsame row handoff)
                (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
                hsame ∧
              UnaryHistory observer ∧ UnaryHistory locality ∧ UnaryHistory invariant ∧
                UnaryHistory audit ∧ UnaryHistory handoff ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _observerLocalityInvariant invariantAuditHandoff handoffPkg
  obtain ⟨observerUnary, invariantUnary, localityUnary, auditUnary, rateUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _localityRoute,
    _auditRoute, provenancePkg, _namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed invariantUnary auditUnary invariantAuditHandoff
  have sourceAtHandoff : hsame handoff handoff ∧ UnaryHistory handoff :=
    ⟨hsame_refl handoff, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observer ∨ hsame row locality ∨ hsame row invariant ∨
              hsame row audit ∨ hsame row rateOrRefusal ∨ hsame row handoff)
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceAtHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert, observerUnary, localityUnary, invariantUnary, auditUnary, handoffUnary,
      provenancePkg⟩

end BEDC.Derived.RelationalPhysicsUp
