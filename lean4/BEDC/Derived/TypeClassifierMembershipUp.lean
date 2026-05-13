import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.TypeClassifierMembershipUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def TypeClassifierMembershipPacket [AskSetup] [PackageSetup]
    (term judgment membership reduction transports routes provenance name : BHist)
    (tag : BMark) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Ext judgment tag membership ∧ Cont term membership reduction ∧
    Cont membership reduction transports ∧ Cont transports routes provenance ∧
      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem TypeClassifierMembershipPacket_subject_reduction_boundary [AskSetup] [PackageSetup]
    {term judgment membership reduction transports routes provenance name membership' reduction' :
      BHist}
    {tag : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeClassifierMembershipPacket term judgment membership reduction transports routes provenance
        name tag bundle pkg ->
      Ext judgment tag membership' ->
        Cont term membership' reduction' ->
          PkgSig bundle reduction' pkg ->
            hsame membership membership' ∧ hsame reduction reduction' ∧
              Cont term membership' reduction' ∧ PkgSig bundle name pkg ∧
                PkgSig bundle reduction' pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Ext Cont hsame
  intro packet membershipBoundary reductionBoundary reductionPkg
  obtain ⟨membershipExt, reductionCont, _transportCont, _routesCont, _provenancePkg,
    namePkg⟩ := packet
  have membershipSame : hsame membership membership' :=
    ext_deterministic membershipExt membershipBoundary
  have reductionSame : hsame reduction reduction' :=
    cont_respects_hsame (hsame_refl term) membershipSame reductionCont reductionBoundary
  exact ⟨membershipSame, reductionSame, reductionBoundary, namePkg, reductionPkg⟩

theorem TypeClassifierMembershipPacket_ext_membership_stability [AskSetup] [PackageSetup]
    {term judgment membership reduction transports routes provenance name membership' reduction'
      transports' : BHist}
    {tag : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeClassifierMembershipPacket term judgment membership reduction transports routes provenance
        name tag bundle pkg →
      Ext judgment tag membership' →
        Cont term membership' reduction' →
          Cont membership' reduction' transports' →
            PkgSig bundle transports' pkg →
              hsame membership membership' ∧ hsame reduction reduction' ∧
                hsame transports transports' ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle transports' pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Ext Cont hsame
  intro packet membershipBoundary reductionBoundary transportBoundary transportPkg
  obtain ⟨membershipExt, reductionCont, transportCont, _routesCont, _provenancePkg,
    namePkg⟩ := packet
  have membershipSame : hsame membership membership' :=
    ext_deterministic membershipExt membershipBoundary
  have reductionSame : hsame reduction reduction' :=
    cont_respects_hsame (hsame_refl term) membershipSame reductionCont reductionBoundary
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame membershipSame reductionSame transportCont transportBoundary
  exact ⟨membershipSame, reductionSame, transportsSame, namePkg, transportPkg⟩

theorem TypeClassifierMembershipPacket_non_escape [AskSetup] [PackageSetup]
    {term judgment membership reduction transports routes provenance name membership' reduction'
      transports' provenance' : BHist}
    {tag : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeClassifierMembershipPacket term judgment membership reduction transports routes provenance
        name tag bundle pkg ->
      Ext judgment tag membership' ->
        Cont term membership' reduction' ->
          Cont membership' reduction' transports' ->
            Cont transports' routes provenance' ->
              PkgSig bundle provenance' pkg ->
                hsame membership membership' ∧ hsame reduction reduction' ∧
                  hsame transports transports' ∧ hsame provenance provenance' ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Ext Cont hsame
  intro packet membershipBoundary reductionBoundary transportBoundary provenanceBoundary
    provenancePkg
  obtain ⟨membershipExt, reductionCont, transportCont, routesCont, _provenancePkg,
    namePkg⟩ := packet
  have membershipSame : hsame membership membership' :=
    ext_deterministic membershipExt membershipBoundary
  have reductionSame : hsame reduction reduction' :=
    cont_respects_hsame (hsame_refl term) membershipSame reductionCont reductionBoundary
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame membershipSame reductionSame transportCont transportBoundary
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame transportsSame (hsame_refl routes) routesCont provenanceBoundary
  exact ⟨membershipSame, reductionSame, transportsSame, provenanceSame, namePkg, provenancePkg⟩

theorem TypeClassifierMembershipPacket_namecert_obligations [AskSetup] [PackageSetup]
    {term judgment membership reduction transports routes provenance name : BHist}
    {tag : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeClassifierMembershipPacket term judgment membership reduction transports routes provenance
        name tag bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          TypeClassifierMembershipPacket term judgment membership reduction transports routes
            provenance name tag bundle pkg ∧ hsame row membership)
        (fun row : BHist =>
          TypeClassifierMembershipPacket term judgment membership reduction transports routes
            provenance name tag bundle pkg ∧ hsame row membership)
        (fun row : BHist =>
          TypeClassifierMembershipPacket term judgment membership reduction transports routes
            provenance name tag bundle pkg ∧ hsame row membership)
        hsame := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg SemanticNameCert hsame
  intro packet
  have sourceMembership :
      (fun row : BHist =>
        TypeClassifierMembershipPacket term judgment membership reduction transports routes
          provenance name tag bundle pkg ∧ hsame row membership) membership := by
    exact And.intro packet (hsame_refl membership)
  have core :
      NameCert
        (fun row : BHist =>
          TypeClassifierMembershipPacket term judgment membership reduction transports routes
            provenance name tag bundle pkg ∧ hsame row membership)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro membership sourceMembership
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRowRow' sameRow'Row''
        exact hsame_trans sameRowRow' sameRow'Row''
      carrier_respects_equiv := by
        intro row row' sameRowRow' sourceRow
        have sameRowMembership : hsame row membership := sourceRow.right
        have sameRow'Membership : hsame row' membership :=
          hsame_trans (hsame_symm sameRowRow') sameRowMembership
        exact And.intro sourceRow.left sameRow'Membership
    }
  exact {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.TypeClassifierMembershipUp
