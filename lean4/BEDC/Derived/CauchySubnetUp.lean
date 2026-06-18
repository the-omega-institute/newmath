import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySubnetCarrier [AskSetup] [PackageSetup]
    (filter subnet window readback tolerance limit sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory filter ∧ UnaryHistory subnet ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory tolerance ∧ UnaryHistory limit ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont filter subnet window ∧
          Cont window readback tolerance ∧ Cont tolerance limit sealRow ∧
            Cont sealRow transport replay ∧ PkgSig bundle provenance pkg

theorem CauchySubnetNameCertObligations [AskSetup] [PackageSetup]
    {F J W R D L E H C P N handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg →
      Cont D L handoff →
        Cont handoff E sealRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                    hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory handoff ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeHandoff routeSeal namePkg
  obtain ⟨unaryF, _unaryJ, _unaryW, _unaryR, unaryD, unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, unaryN, _fjw, _wrd, _dle, _ehc, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryD unaryL routeHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary unaryE routeSeal
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary⟩

theorem CauchySubnet_filter_limit_handoff [AskSetup] [PackageSetup]
    {filter subnet window readback tolerance limit sealRow transport replay provenance localName
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier filter subnet window readback tolerance limit sealRow transport replay
        provenance localName bundle pkg →
      Cont limit sealRow handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row filter ∨ hsame row subnet ∨ hsame row window ∨
                  hsame row readback ∨ hsame row tolerance ∨ hsame row limit ∨
                    hsame row sealRow ∨ hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont limit sealRow handoffRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
              hsame ∧
            UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier limitSealHandoff handoffPkg
  obtain ⟨_filterUnary, _subnetUnary, _windowUnary, _readbackUnary, _toleranceUnary,
    limitUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _filterSubnetWindow, _windowReadbackTolerance, _toleranceLimitSeal,
    _sealTransportReplay, provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed limitUnary sealUnary limitSealHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row subnet ∨ hsame row window ∨
              hsame row readback ∨ hsame row tolerance ∨ hsame row limit ∨
                hsame row sealRow ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont limit sealRow handoffRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, limitSealHandoff, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.CauchySubnetUp
