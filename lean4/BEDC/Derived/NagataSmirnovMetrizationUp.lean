import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

inductive NagataSmirnovMetrizationUp : Type
  | carrier

namespace NagataSmirnovMetrizationUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NagataSmirnovMetrizationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T R L S B E D M F U H C P N coverRead shrinkRead metricRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory R →
        UnaryHistory L →
          UnaryHistory S →
            UnaryHistory B →
              UnaryHistory E →
                UnaryHistory D →
                  UnaryHistory M →
                    UnaryHistory F →
                      UnaryHistory U →
                        UnaryHistory H →
                          UnaryHistory C →
                            Cont T L coverRead →
                              Cont coverRead S shrinkRead →
                                Cont shrinkRead E metricRead →
                                  Cont metricRead M exportRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row exportRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row T ∨ hsame row R ∨ hsame row L ∨
                                                hsame row S ∨ hsame row B ∨
                                                  hsame row E ∨ hsame row D ∨
                                                    hsame row M ∨ hsame row F ∨
                                                      hsame row U ∨ hsame row H ∨
                                                        hsame row C ∨ hsame row exportRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont T L coverRead ∧
                                                Cont coverRead S shrinkRead ∧
                                                  Cont shrinkRead E metricRead ∧
                                                    Cont metricRead M exportRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro tUnary _rUnary lUnary sUnary _bUnary eUnary _dUnary mUnary _fUnary _uUnary
    _hUnary _cUnary coverRoute shrinkRoute metricRoute exportRoute provenancePkg namePkg
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed tUnary lUnary coverRoute
  have shrinkUnary : UnaryHistory shrinkRead :=
    unary_cont_closed coverUnary sUnary shrinkRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed shrinkUnary eUnary metricRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed metricUnary mUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row R ∨ hsame row L ∨ hsame row S ∨ hsame row B ∨
              hsame row E ∨ hsame row D ∨ hsame row M ∨ hsame row F ∨ hsame row U ∨
                hsame row H ∨ hsame row C ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T L coverRead ∧ Cont coverRead S shrinkRead ∧
              Cont shrinkRead E metricRead ∧ Cont metricRead M exportRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, shrinkRoute, metricRoute, exportRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, exportUnary⟩

theorem NagataSmirnovMetrizationCarrier_metric_handoff [AskSetup] [PackageSetup]
    {T R L S B E D M F U H C P N coverRead shrinkRead metricRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory L ->
        UnaryHistory S ->
          UnaryHistory E ->
            UnaryHistory M ->
              Cont T L coverRead ->
                Cont coverRead S shrinkRead ->
                  Cont shrinkRead E metricRead ->
                    Cont metricRead M exportRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row L ∨ hsame row S ∨
                                  hsame row E ∨ hsame row M ∨ hsame row F ∨
                                    hsame row U ∨ hsame row C ∨ hsame row exportRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont T L coverRead ∧
                                  Cont coverRead S shrinkRead ∧
                                    Cont shrinkRead E metricRead ∧
                                      Cont metricRead M exportRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory coverRead ∧ UnaryHistory shrinkRead ∧
                              UnaryHistory metricRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro tUnary lUnary sUnary eUnary mUnary coverRoute shrinkRoute metricRoute exportRoute
    provenancePkg namePkg
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed tUnary lUnary coverRoute
  have shrinkUnary : UnaryHistory shrinkRead :=
    unary_cont_closed coverUnary sUnary shrinkRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed shrinkUnary eUnary metricRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed metricUnary mUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row L ∨ hsame row S ∨ hsame row E ∨ hsame row M ∨
              hsame row F ∨ hsame row U ∨ hsame row C ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T L coverRead ∧ Cont coverRead S shrinkRead ∧
              Cont shrinkRead E metricRead ∧ Cont metricRead M exportRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
        ⟨source.right, coverRoute, shrinkRoute, metricRoute, exportRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, coverUnary, shrinkUnary, metricUnary, exportUnary⟩

end NagataSmirnovMetrizationUp.TasteGate

end BEDC.Derived
