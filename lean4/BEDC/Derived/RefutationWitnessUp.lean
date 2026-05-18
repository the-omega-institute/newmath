import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RefutationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RefutationWitnessCarrier [AskSetup] [PackageSetup]
    (proposition assumption route bottom transport replay provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory proposition ∧ UnaryHistory assumption ∧ UnaryHistory route ∧
    UnaryHistory bottom ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont assumption route bottom ∧ Cont bottom transport replay ∧
          hsame cert replay ∧ PkgSig bundle provenance pkg

theorem RefutationWitnessNameCertObligations [AskSetup] [PackageSetup]
    {proposition assumption route bottom transport replay provenance cert routeRead
      assumptionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RefutationWitnessCarrier proposition assumption route bottom transport replay provenance
        cert bundle pkg ->
      Cont assumption route routeRead ->
        Cont proposition assumption assumptionRead ->
          PkgSig bundle routeRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  RefutationWitnessCarrier proposition assumption route bottom transport replay
                    provenance cert bundle pkg ∧ hsame row cert)
                (fun row : BHist => hsame row cert ∧ UnaryHistory row)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg ∧
                    hsame row cert)
                hsame ∧
              UnaryHistory routeRead ∧ UnaryHistory assumptionRead ∧
                Cont assumption route routeRead ∧ Cont proposition assumption assumptionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrierHyp routeReadCont assumptionReadCont routeReadPkg
  have carrierPacket :
      RefutationWitnessCarrier proposition assumption route bottom transport replay provenance
        cert bundle pkg :=
    carrierHyp
  obtain ⟨propositionUnary, assumptionUnary, routeUnary, _bottomUnary, _transportUnary,
    _replayUnary, _provenanceUnary, certUnary, _bottomRoute, _replayRoute, _certSameReplay,
    provenancePkg⟩ := carrierHyp
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed assumptionUnary routeUnary routeReadCont
  have assumptionReadUnary : UnaryHistory assumptionRead :=
    unary_cont_closed propositionUnary assumptionUnary assumptionReadCont
  have semanticCert :
      SemanticNameCert
          (fun row : BHist =>
            RefutationWitnessCarrier proposition assumption route bottom transport replay
              provenance cert bundle pkg ∧ hsame row cert)
          (fun row : BHist => hsame row cert ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg ∧ hsame row cert)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro cert ⟨carrierPacket, hsame_refl cert⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport certUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, routeReadPkg, source.right⟩
    }
  exact
    ⟨semanticCert, routeReadUnary, assumptionReadUnary, routeReadCont, assumptionReadCont,
      provenancePkg, routeReadPkg⟩

theorem RefutationWitnessCarrier_truth_branch_blocker [AskSetup] [PackageSetup]
    {proposition assumption route bottom transport replay provenance cert truthBranch branchRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : RefutationWitnessCarrier proposition assumption route bottom transport replay
      provenance cert bundle pkg)
    (routeRead : Cont assumption route bottom)
    (branchRead : Cont truthBranch proposition branchRow)
    (sameBranch : hsame truthBranch cert) :
    Cont assumption route bottom ∧ Cont bottom transport replay ∧
      PkgSig bundle provenance pkg ∧ Cont truthBranch proposition branchRow ∧
        hsame truthBranch cert ∧ hsame cert replay ∧ UnaryHistory route ∧
          UnaryHistory cert := by
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg ProbeBundle
  obtain ⟨_propositionUnary, _assumptionUnary, routeUnary, _bottomUnary, _transportUnary,
    _replayUnary, _provenanceUnary, certUnary, _bottomRoute, replayRoute, certReplay,
    provenancePkg⟩ := carrier
  exact
    ⟨routeRead, replayRoute, provenancePkg, branchRead, sameBranch, certReplay, routeUnary,
      certUnary⟩

end BEDC.Derived.RefutationWitnessUp
