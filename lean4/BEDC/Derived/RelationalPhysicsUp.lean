import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont observer locality invariant ∧
        Cont invariant audit rate ∧ Cont transport route provenance ∧
          Cont locality invariant audit ∧ Cont audit rate route ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

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
    _observerLocalityInvariant, _invariantAuditRate, _transportRouteProvenance,
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
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _observerLocalityInvariantFromCarrier, _invariantAuditRate,
    _transportContinuationProvenance, _carrierLocalityInvariantAudit,
    _carrierAuditRateContinuation, provenancePkg, _namePkg⟩ := carrier
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

theorem RelationalPhysicsNameCertObligations [AskSetup] [PackageSetup]
    {observer invariant locality audit rate transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalPhysicsCarrier observer invariant locality audit rate transport route provenance
        name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          RelationalPhysicsCarrier observer invariant locality audit rate transport route
              provenance name bundle pkg ∧
            (hsame row observer ∨ hsame row invariant ∨ hsame row locality ∨
              hsame row audit ∨ hsame row rate))
        (fun _row : BHist =>
          Cont observer locality invariant ∧ Cont invariant audit rate ∧
            Cont transport route provenance ∧ PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness :
      RelationalPhysicsCarrier observer invariant locality audit rate transport route
        provenance name bundle pkg := carrier
  obtain ⟨observerUnary, invariantUnary, localityUnary, auditUnary, rateUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    observerLocalityInvariant, invariantAuditRate, transportRouteProvenance,
    _localityInvariantAudit, _auditRateRoute, provenancePkg, _namePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro observer
          ⟨carrierWitness, Or.inl (hsame_refl observer)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameObserver =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObserver)
          | inr rest =>
              cases rest with
              | inl sameInvariant =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameInvariant))
              | inr rest =>
                  cases rest with
                  | inl sameLocality =>
                      exact Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameLocality)))
                  | inr rest =>
                      cases rest with
                      | inl sameAudit =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameAudit))))
                      | inr sameRate =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (hsame_trans (hsame_symm sameRows) sameRate))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨observerLocalityInvariant, invariantAuditRate, transportRouteProvenance,
          provenancePkg⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl sameObserver =>
          exact ⟨unary_transport observerUnary (hsame_symm sameObserver), provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameInvariant =>
              exact
                ⟨unary_transport invariantUnary (hsame_symm sameInvariant), provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameLocality =>
                  exact
                    ⟨unary_transport localityUnary (hsame_symm sameLocality), provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameAudit =>
                      exact
                        ⟨unary_transport auditUnary (hsame_symm sameAudit), provenancePkg⟩
                  | inr sameRate =>
                      exact
                        ⟨unary_transport rateUnary (hsame_symm sameRate), provenancePkg⟩
  }

theorem RelationalPhysicsGlobalFrameTailExclusion [AskSetup] [PackageSetup]
    {observer invariant locality audit rate transport route provenance name invariantRead
      auditRead frameRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalPhysicsCarrier observer invariant locality audit rate transport route provenance
        name bundle pkg →
      Cont observer locality invariantRead →
        Cont invariantRead audit auditRead →
          Cont auditRead rate frameRead →
            PkgSig bundle frameRead pkg →
              hsame invariantRead invariant ∧ UnaryHistory auditRead ∧
                UnaryHistory frameRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle frameRead pkg ∧
                    (Cont frameRead (BHist.e0 hostTail) auditRead → False) ∧
                      (Cont frameRead (BHist.e1 hostTail) auditRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier observerLocalityInvariantRead invariantReadAuditRead auditReadRateFrame
    framePkg
  obtain ⟨observerUnary, _invariantUnary, localityUnary, auditUnary, rateUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    observerLocalityInvariant, _invariantAuditRate, _transportRouteProvenance,
    _localityInvariantAudit, _auditRateRoute, provenancePkg, _namePkg⟩ := carrier
  have invariantReadSame : hsame invariantRead invariant :=
    cont_deterministic observerLocalityInvariantRead observerLocalityInvariant
  have invariantReadUnary : UnaryHistory invariantRead :=
    unary_cont_closed observerUnary localityUnary observerLocalityInvariantRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed invariantReadUnary auditUnary invariantReadAuditRead
  have frameReadUnary : UnaryHistory frameRead :=
    unary_cont_closed auditReadUnary rateUnary auditReadRateFrame
  exact
    ⟨invariantReadSame, auditReadUnary, frameReadUnary, provenancePkg, framePkg,
      cont_mutual_extension_right_tail_absurd.left auditReadRateFrame,
      cont_mutual_extension_right_tail_absurd.right auditReadRateFrame⟩

end BEDC.Derived.RelationalPhysicsUp
