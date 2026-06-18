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

theorem ClassifierBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source accepted refused preserved sig transport route provenance nameCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierBoundaryCarrier source accepted refused preserved sig transport route provenance
        nameCert bundle pkg ->
      SigRel bundle source sig ->
        Cont accepted route preserved ->
          Cont sig route publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead)
                  (fun row : BHist => hsame row publicRead)
                  (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                Ext source BMark.b0 accepted ∧ Ext source BMark.b1 refused ∧
                  SigRel bundle source sig ∧ Cont accepted route preserved ∧
                    Cont sig route publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle nameCert pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel PkgSig hsame SemanticNameCert
  intro carrier sigRead acceptedRoute publicRoute publicPkg
  obtain ⟨acceptedExt, refusedExt, _preservedRoute, _transportSelf, _sigSelf,
    provenancePkg, nameCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (hsame_refl publicRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨source, publicPkg⟩
  }
  exact
    ⟨cert, acceptedExt, refusedExt, sigRead, acceptedRoute, publicRoute, provenancePkg,
      nameCertPkg, publicPkg⟩

theorem ClassifierBoundaryCarrier_public_boundary [AskSetup] [PackageSetup]
    {source accepted refused preserved sig transport route provenance nameCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierBoundaryCarrier source accepted refused preserved sig transport route provenance
        nameCert bundle pkg →
      Ext source BMark.b0 accepted →
        Ext source BMark.b1 refused →
          Cont accepted route preserved →
            SigRel bundle source sig →
              Cont sig route publicRead →
                PkgSig bundle publicRead pkg →
                  Ext source BMark.b0 accepted ∧ Ext source BMark.b1 refused ∧
                    Cont accepted route preserved ∧ SigRel bundle source sig ∧
                      Cont sig route publicRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle nameCert pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel PkgSig
  intro carrier acceptedExt refusedExt acceptedRoute sigRead publicRoute publicPkg
  obtain ⟨_carrierAcceptedExt, _carrierRefusedExt, _carrierAcceptedRoute,
    _transportSelf, _sigSelf, provenancePkg, nameCertPkg⟩ := carrier
  exact
    ⟨acceptedExt, refusedExt, acceptedRoute, sigRead, publicRoute, provenancePkg,
      nameCertPkg, publicPkg⟩

end BEDC.Derived.ClassifierBoundaryUp
