import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive AssouadSnowflakeEmbeddingUp : Type where
  | mk (M D A S E B Q R H C P N : BHist) : AssouadSnowflakeEmbeddingUp

namespace AssouadSnowflakeEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AssouadSnowflakeEmbeddingCarrier (M D A S E B Q R H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory S ∧
    UnaryHistory E ∧ UnaryHistory B ∧ UnaryHistory Q ∧ UnaryHistory R ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N

theorem AssouadSnowflakeEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M D A S E B Q R H C P N md da snow embed centers tol realRead
      transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AssouadSnowflakeEmbeddingCarrier M D A S E B Q R H C P N →
      Cont M D md →
        Cont md A da →
          Cont da S snow →
            Cont snow E embed →
              Cont embed B centers →
                Cont centers Q tol →
                  Cont tol R realRead →
                    Cont realRead H transportedRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row D ∨ hsame row A ∨ hsame row S ∨
                                  hsame row E ∨ hsame row B ∨ hsame row Q ∨ hsame row R ∨
                                    hsame row H ∨ hsame row P ∨ hsame row N ∨
                                      hsame row transportedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M D md ∧ Cont md A da ∧
                                  Cont da S snow ∧ Cont snow E embed ∧ Cont embed B centers ∧
                                    Cont centers Q tol ∧ Cont tol R realRead ∧
                                      Cont realRead H transportedRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory md ∧ UnaryHistory da ∧ UnaryHistory snow ∧
                              UnaryHistory embed ∧ UnaryHistory centers ∧ UnaryHistory tol ∧
                                UnaryHistory realRead ∧ UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier mdRoute daRoute snowRoute embedRoute centersRoute tolRoute realReadRoute
    transportedRoute provenancePkg namePkg
  obtain ⟨mUnary, dUnary, aUnary, sUnary, eUnary, bUnary, qUnary, rUnary, hUnary,
    _cUnary, _pUnary, _nUnary⟩ := carrier
  have mdUnary : UnaryHistory md :=
    unary_cont_closed mUnary dUnary mdRoute
  have daUnary : UnaryHistory da :=
    unary_cont_closed mdUnary aUnary daRoute
  have snowUnary : UnaryHistory snow :=
    unary_cont_closed daUnary sUnary snowRoute
  have embedUnary : UnaryHistory embed :=
    unary_cont_closed snowUnary eUnary embedRoute
  have centersUnary : UnaryHistory centers :=
    unary_cont_closed embedUnary bUnary centersRoute
  have tolUnary : UnaryHistory tol :=
    unary_cont_closed centersUnary qUnary tolRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tolUnary rUnary realReadRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed realReadUnary hUnary transportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row A ∨ hsame row S ∨
              hsame row E ∨ hsame row B ∨ hsame row Q ∨ hsame row R ∨
                hsame row H ∨ hsame row P ∨ hsame row N ∨
                  hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D md ∧ Cont md A da ∧
              Cont da S snow ∧ Cont snow E embed ∧ Cont embed B centers ∧
                Cont centers Q tol ∧ Cont tol R realRead ∧
                  Cont realRead H transportedRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, mdRoute, daRoute, snowRoute, embedRoute, centersRoute, tolRoute,
          realReadRoute, transportedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, mdUnary, daUnary, snowUnary, embedUnary, centersUnary, tolUnary, realReadUnary,
      transportedUnary⟩

theorem AssouadSnowflakeEmbeddingCarrier_finite_net_handoff [AskSetup] [PackageSetup]
    {M D A S E B Q R H C P N coverRead scaleRead netRead snowflakeRead distanceRead
      embeddingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AssouadSnowflakeEmbeddingCarrier M D A S E B Q R H C P N →
      Cont M D coverRead →
        Cont coverRead A scaleRead →
          Cont scaleRead E netRead →
            Cont S Q snowflakeRead →
              Cont snowflakeRead R distanceRead →
                Cont netRead distanceRead embeddingRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle embeddingRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row embeddingRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row D ∨ hsame row A ∨ hsame row S ∨
                              hsame row E ∨ hsame row Q ∨ hsame row R ∨
                                hsame row embeddingRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M D coverRead ∧
                              Cont coverRead A scaleRead ∧ Cont scaleRead E netRead ∧
                                Cont S Q snowflakeRead ∧ Cont snowflakeRead R distanceRead ∧
                                  Cont netRead distanceRead embeddingRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle embeddingRead pkg)
                          hsame ∧
                        UnaryHistory embeddingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute scaleRoute netRoute snowflakeRoute distanceRoute embeddingRoute
    provenancePkg embeddingPkg
  obtain ⟨mUnary, dUnary, aUnary, sUnary, eUnary, _bUnary, qUnary, rUnary, _hUnary,
    _cUnary, _pUnary, _nUnary⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary dUnary coverRoute
  have scaleReadUnary : UnaryHistory scaleRead :=
    unary_cont_closed coverReadUnary aUnary scaleRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed scaleReadUnary eUnary netRoute
  have snowflakeReadUnary : UnaryHistory snowflakeRead :=
    unary_cont_closed sUnary qUnary snowflakeRoute
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed snowflakeReadUnary rUnary distanceRoute
  have embeddingReadUnary : UnaryHistory embeddingRead :=
    unary_cont_closed netReadUnary distanceReadUnary embeddingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row embeddingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row A ∨ hsame row S ∨
              hsame row E ∨ hsame row Q ∨ hsame row R ∨ hsame row embeddingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D coverRead ∧
              Cont coverRead A scaleRead ∧ Cont scaleRead E netRead ∧
                Cont S Q snowflakeRead ∧ Cont snowflakeRead R distanceRead ∧
                  Cont netRead distanceRead embeddingRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle embeddingRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro embeddingRead ⟨hsame_refl embeddingRead, embeddingReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, scaleRoute, netRoute, snowflakeRoute, distanceRoute,
          embeddingRoute, provenancePkg, embeddingPkg⟩
  }
  exact ⟨cert, embeddingReadUnary⟩

end AssouadSnowflakeEmbeddingUp

end BEDC.Derived
