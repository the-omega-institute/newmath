import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClassifierBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

def ClassifierBoundaryCarrier [AskSetup] [PackageSetup]
    (source accepted refused preserved sig transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Ext source BMark.b0 accepted ∧ Ext source BMark.b1 refused ∧
    Cont accepted route preserved ∧ hsame transport transport ∧ hsame sig sig ∧
      PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem ClassifierBoundaryCarrier_sigrel_consumer_determinacy [AskSetup] [PackageSetup]
    {source accepted refused preserved sig transport route provenance nameCert read read' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierBoundaryCarrier source accepted refused preserved sig transport route provenance
        nameCert bundle pkg ->
      SigRel bundle source read ->
        SigRel bundle source read' ->
          hsame read sig ->
            hsame read' sig ->
              hsame read read' /\ PkgSig bundle provenance pkg /\
                PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel PkgSig hsame
  intro carrier _readRel _readRel' readSameSig read'SameSig
  obtain ⟨_acceptedExt, _refusedExt, _preservedRoute, _transportSelf, _sigSelf,
    provenancePkg, nameCertPkg⟩ := carrier
  have readSameRead' : hsame read read' :=
    hsame_trans readSameSig (hsame_symm read'SameSig)
  exact ⟨readSameRead', provenancePkg, nameCertPkg⟩

end BEDC.Derived.ClassifierBoundaryUp
