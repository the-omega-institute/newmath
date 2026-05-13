import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.TypeClassifierMembershipUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
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

end BEDC.Derived.TypeClassifierMembershipUp
