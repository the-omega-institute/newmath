import BEDC.Derived.CauchyCompletionComparisonUp.CarrierAlignment
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

instance cauchyCompletionComparisonBHistCarrier : BHistCarrier CauchyCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionComparisonToEventFlow
  fromEventFlow := cauchyCompletionComparisonFromEventFlow

instance cauchyCompletionComparisonChapterTasteGate :
    ChapterTasteGate CauchyCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow x) =
        some x
    exact CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionComparisonTasteGate_single_carrier_alignment_injective heq)

def CauchyCompletionComparisonCarrier [AskSetup] [PackageSetup]
    (unit universal functorial metric regular stream dyadic realSeal transport replay provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  UnaryHistory unit ∧ UnaryHistory universal ∧ UnaryHistory functorial ∧
    UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory stream ∧
      UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont unit universal transport ∧ Cont transport functorial replay ∧
            Cont stream dyadic provenance ∧ Cont regular realSeal name ∧
              PkgSig bundle name pkg

theorem CauchyCompletionComparisonCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {unit universal functorial metric regular stream dyadic realSeal transport replay provenance name
      routeA routeB routeC : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionComparisonCarrier unit universal functorial metric regular stream dyadic
        realSeal transport replay provenance name bundle pkg →
      Cont unit universal routeA →
        Cont routeA functorial routeB →
          Cont stream dyadic routeC →
            PkgSig bundle name pkg →
              UnaryHistory unit ∧ UnaryHistory universal ∧ UnaryHistory functorial ∧
                UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory stream ∧
                  UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory routeA ∧
                    UnaryHistory routeB ∧ UnaryHistory routeC ∧
                      Cont unit universal routeA ∧ Cont routeA functorial routeB ∧
                        Cont stream dyadic routeC ∧ PkgSig bundle name pkg ∧
                          SemanticNameCert
                            (fun row : BHist =>
                              hsame row routeB ∨ hsame row routeC ∨ hsame row realSeal ∨
                                hsame row name)
                            (fun row : BHist =>
                              Cont unit universal routeA ∧
                                Cont routeA functorial routeB ∧
                                  Cont stream dyadic routeC ∧
                                    (hsame row routeB ∨ hsame row routeC ∨
                                      hsame row realSeal ∨ hsame row name))
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier unitRoute functorialRoute streamRoute pkgSig
  obtain ⟨unitUnary, universalUnary, functorialUnary, metricUnary, regularUnary, streamUnary,
    dyadicUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
    _carrierUnitRoute, _carrierFunctorialRoute, _carrierStreamRoute, _carrierSealRoute,
    _carrierPkg⟩ := carrier
  have routeAUnary : UnaryHistory routeA :=
    unary_cont_closed unitUnary universalUnary unitRoute
  have routeBUnary : UnaryHistory routeB :=
    unary_cont_closed routeAUnary functorialUnary functorialRoute
  have routeCUnary : UnaryHistory routeC :=
    unary_cont_closed streamUnary dyadicUnary streamRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row routeB ∨ hsame row routeC ∨ hsame row realSeal ∨ hsame row name)
        (fun row : BHist =>
          Cont unit universal routeA ∧ Cont routeA functorial routeB ∧
            Cont stream dyadic routeC ∧
              (hsame row routeB ∨ hsame row routeC ∨ hsame row realSeal ∨ hsame row name))
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro routeB (Or.inl (hsame_refl routeB))
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
          intro _row _other same sourceSpec
          cases sourceSpec with
          | inl sameRouteB =>
              exact Or.inl (hsame_trans (hsame_symm same) sameRouteB)
          | inr rest =>
              cases rest with
              | inl sameRouteC =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameRouteC))
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameSeal)))
                  | inr sameName =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm same) sameName)))
      }
      pattern_sound := by
        intro _row sourceSpec
        exact ⟨unitRoute, functorialRoute, streamRoute, sourceSpec⟩
      ledger_sound := by
        intro row sourceSpec
        have rowUnary : UnaryHistory row := by
          cases sourceSpec with
          | inl sameRouteB =>
              exact unary_transport routeBUnary (hsame_symm sameRouteB)
          | inr rest =>
              cases rest with
              | inl sameRouteC =>
                  exact unary_transport routeCUnary (hsame_symm sameRouteC)
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact unary_transport sealUnary (hsame_symm sameSeal)
                  | inr sameName =>
                      exact unary_transport nameUnary (hsame_symm sameName)
        exact ⟨rowUnary, pkgSig⟩
    }
  exact
    ⟨unitUnary, universalUnary, functorialUnary, metricUnary, regularUnary, streamUnary,
      dyadicUnary, sealUnary, routeAUnary, routeBUnary, routeCUnary, unitRoute,
      functorialRoute, streamRoute, pkgSig, cert⟩

end BEDC.Derived.CauchyCompletionComparisonUp
