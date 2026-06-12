import BEDC.Derived.HyperbolicGeodesicFlowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperbolicGeodesicFlowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HyperbolicGeodesicFlowCarrier [AskSetup] [PackageSetup]
    (U M B T D F J A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  hyperbolicGeodesicFlowFields
      (HyperbolicGeodesicFlowUp.mk U M B T D F J A H C P N) =
    [U, M, B, T, D, F, J, A, H, C, P, N] ∧
    UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory T ∧
      UnaryHistory D ∧ UnaryHistory F ∧ UnaryHistory J ∧ UnaryHistory A ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle P pkg

theorem HyperbolicGeodesicFlowFixedEndNonescape [AskSetup] [PackageSetup]
    {geodesic endpoint boundary flow provenance name fixedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory geodesic ->
      UnaryHistory endpoint ->
        UnaryHistory boundary ->
          UnaryHistory flow ->
            Cont geodesic endpoint fixedRead ->
              Cont fixedRead flow replayRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle name pkg ->
                    UnaryHistory fixedRead ∧ UnaryHistory replayRead ∧
                      Cont geodesic endpoint fixedRead ∧ Cont fixedRead flow replayRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro geodesicUnary endpointUnary _boundaryUnary flowUnary fixedRoute replayRoute
    provenancePkg namePkg
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed geodesicUnary endpointUnary fixedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed fixedUnary flowUnary replayRoute
  exact
    ⟨fixedUnary, replayUnary, fixedRoute, replayRoute, provenancePkg, namePkg⟩

theorem HyperbolicGeodesicFlowNamecertObligations [AskSetup] [PackageSetup]
    {U M B T D F J A H C P N diskMetric boundaryFlow fixedAudit namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperbolicGeodesicFlowCarrier U M B T D F J A H C P N bundle pkg →
      Cont U M diskMetric →
        Cont B T boundaryFlow →
          Cont D F fixedAudit →
            Cont fixedAudit N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row M ∨ hsame row B ∨ hsame row T ∨
                        hsame row D ∨ hsame row F ∨ hsame row J ∨ hsame row A ∨
                          hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U M diskMetric ∧ Cont B T boundaryFlow ∧
                        Cont D F fixedAudit ∧ Cont fixedAudit N namedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory diskMetric ∧ UnaryHistory boundaryFlow ∧
                    UnaryHistory fixedAudit ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier diskRoute boundaryRoute fixedRoute namedRoute namedPkg
  obtain ⟨fieldRows, uUnary, mUnary, bUnary, tUnary, dUnary, fUnary, _jUnary,
    _aUnary, _hUnary, _cUnary, _pUnary, nUnary, pPkg⟩ := carrier
  cases fieldRows
  have diskUnary : UnaryHistory diskMetric :=
    unary_cont_closed uUnary mUnary diskRoute
  have boundaryUnary : UnaryHistory boundaryFlow :=
    unary_cont_closed bUnary tUnary boundaryRoute
  have fixedUnary : UnaryHistory fixedAudit :=
    unary_cont_closed dUnary fUnary fixedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed fixedUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row M ∨ hsame row B ∨ hsame row T ∨
              hsame row D ∨ hsame row F ∨ hsame row J ∨ hsame row A ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U M diskMetric ∧ Cont B T boundaryFlow ∧
              Cont D F fixedAudit ∧ Cont fixedAudit N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diskRoute, boundaryRoute, fixedRoute, namedRoute, pPkg, namedPkg⟩
  }
  exact ⟨cert, diskUnary, boundaryUnary, fixedUnary, namedUnary⟩

end BEDC.Derived.HyperbolicGeodesicFlowUp
