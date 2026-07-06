import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalEmbeddingCarrier [AskSetup] [PackageSetup]
    (q S R D E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RationalEmbeddingCarrier_constant_sequence_route [AskSetup] [PackageSetup]
    {q S R D E H C P N scheduleRead readbackRead dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg →
      Cont q S scheduleRead →
        Cont scheduleRead R readbackRead →
          Cont readbackRead D dyadicRead →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row R ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                      hsame row dyadicRead)
                  (fun _row : BHist =>
                    UnaryHistory _row ∧ Cont q S scheduleRead ∧
                      Cont scheduleRead R readbackRead ∧ Cont readbackRead D dyadicRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory dyadicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeSchedule routeReadback routeDyadic provenance
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, _unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryR routeReadback
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD routeDyadic
  have sourceR :
      (fun row : BHist => hsame row R ∧ UnaryHistory row) R := by
    exact ⟨hsame_refl R, unaryR⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row dyadicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S scheduleRead ∧
              Cont scheduleRead R readbackRead ∧ Cont readbackRead D dyadicRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro R sourceR
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSchedule, routeReadback, routeDyadic, provenance⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, dyadicUnary⟩

theorem RationalEmbeddingRealSealBoundary [AskSetup] [PackageSetup]
    {q S R D E H C P N scheduleRead readbackRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg ->
      Cont q S scheduleRead ->
        Cont scheduleRead R readbackRead ->
          Cont readbackRead D dyadicRead ->
            Cont dyadicRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                        hsame row E ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont q S scheduleRead ∧
                        Cont scheduleRead R readbackRead ∧
                          Cont readbackRead D dyadicRead ∧
                            Cont dyadicRead E sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeSchedule routeReadback routeDyadic routeSeal sealPkg
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryR routeReadback
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD routeDyadic
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryE routeSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S scheduleRead ∧
              Cont scheduleRead R readbackRead ∧
                Cont readbackRead D dyadicRead ∧
                  Cont dyadicRead E sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeSchedule, routeReadback, routeDyadic, routeSeal, sealPkg⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, dyadicUnary, sealUnary⟩

theorem RationalEmbeddingStationaryReadbackExactness [AskSetup] [PackageSetup]
    {q S R D E H C P N qSchedule stationary dyadicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory D →
            Cont q S qSchedule →
              Cont qSchedule R stationary →
                Cont stationary D dyadicSeal →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row stationary ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row q ∨ hsame row S ∨ hsame row R ∨
                              hsame row qSchedule ∨ hsame row stationary)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont q S qSchedule ∧
                              Cont qSchedule R stationary ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory qSchedule ∧ UnaryHistory stationary := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro unaryQ unaryS unaryR _unaryD routeSchedule routeStationary _routeDyadic sourcePkg namePkg
  have scheduleUnary : UnaryHistory qSchedule :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed scheduleUnary unaryR routeStationary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stationary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨
              hsame row qSchedule ∨ hsame row stationary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S qSchedule ∧
              Cont qSchedule R stationary ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stationary
        ⟨hsame_refl stationary, stationaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSchedule, routeStationary, sourcePkg, namePkg⟩
  }
  exact ⟨cert, scheduleUnary, stationaryUnary⟩

theorem RationalEmbeddingStreamNameScope [AskSetup] [PackageSetup]
    {q S R D E H C P N qSchedule stationary dyadicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg ->
      Cont q S qSchedule ->
        Cont qSchedule R stationary ->
          Cont stationary D dyadicSeal ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row S ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row q ∨ hsame row S ∨ hsame row qSchedule ∨
                      hsame row stationary ∨ hsame row dyadicSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont q S qSchedule ∧
                      Cont qSchedule R stationary ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory qSchedule ∧ UnaryHistory stationary ∧
                  UnaryHistory dyadicSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeSchedule routeStationary routeDyadic namePkg
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, _unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory qSchedule :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed scheduleUnary unaryR routeStationary
  have dyadicUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed stationaryUnary unaryD routeDyadic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row qSchedule ∨
              hsame row stationary ∨ hsame row dyadicSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S qSchedule ∧
              Cont qSchedule R stationary ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, unaryS⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSchedule, routeStationary, namePkg⟩
  }
  exact ⟨cert, scheduleUnary, stationaryUnary, dyadicUnary⟩

theorem RationalEmbeddingNameCertObligations [AskSetup] [PackageSetup]
    {q S R D E H C P N qSchedule stationary dyadicSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg ->
      Cont q S qSchedule ->
        Cont qSchedule R stationary ->
          Cont stationary D dyadicSeal ->
            Cont dyadicSeal E sealRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont q S qSchedule ∧
                          Cont qSchedule R stationary ∧
                            Cont stationary D dyadicSeal ∧
                              Cont dyadicSeal E sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory qSchedule ∧ UnaryHistory stationary ∧
                      UnaryHistory dyadicSeal ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeSchedule routeStationary routeDyadic routeSeal sourcePkg namePkg
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, unaryE, _unaryH, _unaryC, _unaryP,
    unaryN, _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory qSchedule :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed scheduleUnary unaryR routeStationary
  have dyadicUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed stationaryUnary unaryD routeDyadic
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryE routeSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S qSchedule ∧
              Cont qSchedule R stationary ∧
                Cont stationary D dyadicSeal ∧
                  Cont dyadicSeal E sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeSchedule, routeStationary, routeDyadic, routeSeal, sourcePkg,
          namePkg⟩
  }
  exact ⟨cert, scheduleUnary, stationaryUnary, dyadicUnary, sealUnary⟩

theorem RationalEmbeddingNonescape [AskSetup] [PackageSetup]
    {q S R D E H C P N qSchedule stationary dyadicSeal sealRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg ->
      Cont q S qSchedule ->
        Cont qSchedule R stationary ->
          Cont stationary D dyadicSeal ->
            Cont dyadicSeal E sealRead ->
              Cont sealRead N consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
                    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
                      UnaryHistory N ∧ UnaryHistory qSchedule ∧
                        UnaryHistory stationary ∧ UnaryHistory dyadicSeal ∧
                          UnaryHistory sealRead ∧ UnaryHistory consumerRead ∧
                            Cont q S qSchedule ∧ Cont qSchedule R stationary ∧
                              Cont stationary D dyadicSeal ∧ Cont dyadicSeal E sealRead ∧
                                Cont sealRead N consumerRead ∧
                                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier routeSchedule routeStationary routeDyadic routeSeal routeConsumer consumerPkg
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, unaryE, unaryH, unaryC, unaryP, unaryN,
    _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory qSchedule :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed scheduleUnary unaryR routeStationary
  have dyadicUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed stationaryUnary unaryD routeDyadic
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryE routeSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary unaryN routeConsumer
  exact
    ⟨unaryQ, unaryS, unaryR, unaryD, unaryE, unaryH, unaryC, unaryP, unaryN,
      scheduleUnary, stationaryUnary, dyadicUnary, sealUnary, consumerUnary, routeSchedule,
      routeStationary, routeDyadic, routeSeal, routeConsumer, consumerPkg⟩

end BEDC.Derived.RationalEmbeddingUp
