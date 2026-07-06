import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZetaContinuationSocketCarrier [AskSetup] [PackageSetup]
    (basic eta analytic pole functional trivial gamma transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory basic ∧ UnaryHistory eta ∧ UnaryHistory analytic ∧ UnaryHistory pole ∧
    UnaryHistory functional ∧ UnaryHistory trivial ∧ UnaryHistory gamma ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory name ∧
        Cont basic eta analytic ∧ Cont pole functional trivial ∧
          Cont gamma transport route ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem ZetaContinuationSocketNameCertObligations [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
      route name bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame ∧ UnaryHistory analytic ∧ UnaryHistory functional ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, functionalUnary,
    _trivialUnary, _gammaUnary, _transportUnary, routeUnary, nameUnary, analyticRoute,
    trivialRoute, routeRoute, routePkg, namePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, analyticRoute, trivialRoute, routeRoute, routePkg, namePkg⟩
  }
  exact ⟨cert, analyticUnary, functionalUnary, routeUnary⟩

theorem ZetaContinuationSocketLedger_nonescape [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
      route name bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row pole ∨ hsame row gamma ∨ hsame row trivial)
          (fun row : BHist =>
            hsame row pole ∨ hsame row gamma ∨ hsame row trivial ∨ hsame row analytic ∨
              hsame row route)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame ∧ UnaryHistory pole ∧ UnaryHistory gamma ∧ UnaryHistory trivial := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, poleUnary, _functionalUnary,
    trivialUnary, gammaUnary, _transportUnary, routeUnary, _nameUnary, _analyticRoute,
    _trivialRoute, _routeRoute, routePkg, namePkg⟩ := carrier
  have sourcePole :
      (fun row : BHist => hsame row pole ∨ hsame row gamma ∨ hsame row trivial) pole :=
    Or.inl (hsame_refl pole)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pole ∨ hsame row gamma ∨ hsame row trivial)
          (fun row : BHist =>
            hsame row pole ∨ hsame row gamma ∨ hsame row trivial ∨ hsame row analytic ∨
              hsame row route)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨pole, sourcePole⟩
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
        cases source with
        | inl samePole =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) samePole)
        | inr tail =>
            cases tail with
            | inl sameGamma =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma))
            | inr sameTrivial =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) sameTrivial))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl samePole =>
          exact Or.inl samePole
      | inr tail =>
          cases tail with
          | inl sameGamma =>
              exact Or.inr (Or.inl sameGamma)
          | inr sameTrivial =>
              exact Or.inr (Or.inr (Or.inl sameTrivial))
    ledger_sound := by
      intro row source
      cases source with
      | inl samePole =>
          exact ⟨unary_transport poleUnary (hsame_symm samePole), routePkg, namePkg⟩
      | inr tail =>
          cases tail with
          | inl sameGamma =>
              exact ⟨unary_transport gammaUnary (hsame_symm sameGamma), routePkg, namePkg⟩
          | inr sameTrivial =>
              exact
                ⟨unary_transport trivialUnary (hsame_symm sameTrivial), routePkg, namePkg⟩
  }
  exact ⟨cert, poleUnary, gammaUnary, trivialUnary⟩

theorem ZetaContinuationSocketWitnessCarrierBridge [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name witnessPkg
      witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg →
      UnaryHistory witnessPkg →
        PkgSig bundle witnessPkg pkg →
          Cont route witnessPkg witnessRead →
            SemanticNameCert
                (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
                    hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                      hsame row transport ∨ hsame row route ∨ hsame row witnessPkg ∨
                        hsame row name ∨ hsame row witnessRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont basic eta analytic ∧
                    Cont pole functional trivial ∧ Cont gamma transport route ∧
                      Cont route witnessPkg witnessRead ∧ PkgSig bundle route pkg ∧
                        PkgSig bundle witnessPkg pkg ∧ PkgSig bundle name pkg)
                hsame ∧
              UnaryHistory analytic ∧ UnaryHistory route ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier witnessUnary witnessPkgSig witnessRoute
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, _functionalUnary,
    _trivialUnary, _gammaUnary, _transportUnary, routeUnary, _nameUnary, analyticRoute,
    trivialRoute, routeRoute, routePkg, namePkg⟩ := carrier
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed routeUnary witnessUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row witnessPkg ∨
                  hsame row name ∨ hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                Cont route witnessPkg witnessRead ∧ PkgSig bundle route pkg ∧
                  PkgSig bundle witnessPkg pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessReadUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, analyticRoute, trivialRoute, routeRoute, witnessRoute, routePkg,
          witnessPkgSig, namePkg⟩
  }
  exact ⟨cert, analyticUnary, routeUnary, witnessReadUnary⟩

theorem ZetaContinuationSocketCarrier_boundary_exhaustion [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name analyticRead
      sealRead witnessPkg witnessRead functionalRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg →
      Cont analytic route analyticRead →
        Cont analyticRead name sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory witnessPkg →
              PkgSig bundle witnessPkg pkg →
                Cont route witnessPkg witnessRead →
                  Cont functional gamma functionalRead →
                    Cont functionalRead route finalRead →
                      PkgSig bundle finalRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨
                                hsame row route ∨ hsame row name ∨
                                  hsame row analyticRead ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont analytic route analyticRead ∧
                                Cont analyticRead name sealRead ∧
                                  PkgSig bundle sealRead pkg)
                            hsame ∧
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row witnessRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨
                                  hsame row pole ∨ hsame row functional ∨
                                    hsame row trivial ∨ hsame row gamma ∨
                                      hsame row transport ∨ hsame row route ∨
                                        hsame row witnessPkg ∨ hsame row name ∨
                                          hsame row witnessRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont basic eta analytic ∧
                                  Cont pole functional trivial ∧
                                    Cont gamma transport route ∧
                                      Cont route witnessPkg witnessRead ∧
                                        PkgSig bundle route pkg ∧
                                          PkgSig bundle witnessPkg pkg ∧
                                            PkgSig bundle name pkg)
                              hsame ∧
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row finalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row basic ∨ hsame row eta ∨
                                    hsame row analytic ∨ hsame row pole ∨
                                      hsame row functional ∨ hsame row trivial ∨
                                        hsame row gamma ∨ hsame row transport ∨
                                          hsame row route ∨ hsame row name ∨
                                            hsame row functionalRead ∨
                                              hsame row finalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont functional gamma functionalRead ∧
                                    Cont functionalRead route finalRead ∧
                                      PkgSig bundle finalRead pkg)
                                hsame ∧
                              UnaryHistory sealRead ∧ UnaryHistory witnessRead ∧
                                UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: ZetaContinuationSocketCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier analyticReadRoute sealRoute sealPkg witnessUnary witnessPkgSig witnessRoute
    functionalRoute finalRoute finalPkg
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, functionalUnary,
    _trivialUnary, gammaUnary, _transportUnary, routeUnary, nameUnary, analyticRoute,
    trivialRoute, routeRoute, routePkg, namePkg⟩ := carrier
  have analyticReadUnary : UnaryHistory analyticRead :=
    unary_cont_closed analyticUnary routeUnary analyticReadRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed analyticReadUnary nameUnary sealRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed routeUnary witnessUnary witnessRoute
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed functionalReadUnary routeUnary finalRoute
  have sealCert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row route ∨
              hsame row name ∨ hsame row analyticRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont analytic route analyticRead ∧
              Cont analyticRead name sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, analyticReadRoute, sealRoute, sealPkg⟩
  }
  have witnessCert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row witnessPkg ∨
                  hsame row name ∨ hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                Cont route witnessPkg witnessRead ∧ PkgSig bundle route pkg ∧
                  PkgSig bundle witnessPkg pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessReadUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, analyticRoute, trivialRoute, routeRoute, witnessRoute, routePkg,
          witnessPkgSig, namePkg⟩
  }
  have finalCert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name ∨
                  hsame row functionalRead ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont functional gamma functionalRead ∧
              Cont functionalRead route finalRead ∧ PkgSig bundle finalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, functionalRoute, finalRoute, finalPkg⟩
  }
  exact ⟨sealCert, witnessCert, finalCert, sealUnary, witnessReadUnary, finalReadUnary⟩

theorem ZetaContinuationSocketCarrier_obligation_package [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name analyticRead
      sealRead witnessPkg witnessRead functionalRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg ->
      Cont analytic route analyticRead ->
        Cont analyticRead name sealRead ->
          UnaryHistory witnessPkg ->
            PkgSig bundle witnessPkg pkg ->
              Cont route witnessPkg witnessRead ->
                Cont functional gamma functionalRead ->
                  Cont functionalRead route finalRead ->
                    PkgSig bundle finalRead pkg ->
                      UnaryHistory analyticRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory witnessRead ∧ UnaryHistory functionalRead ∧
                          UnaryHistory finalRead ∧ PkgSig bundle route pkg ∧
                            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier analyticReadRoute sealRoute witnessUnary _witnessPkgSig witnessRoute
    functionalRoute finalRoute _finalPkg
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, functionalUnary,
    _trivialUnary, gammaUnary, _transportUnary, routeUnary, nameUnary, _analyticRoute,
    _trivialRoute, _routeRoute, routePkg, namePkg⟩ := carrier
  have analyticReadUnary : UnaryHistory analyticRead :=
    unary_cont_closed analyticUnary routeUnary analyticReadRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed analyticReadUnary nameUnary sealRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed routeUnary witnessUnary witnessRoute
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed functionalReadUnary routeUnary finalRoute
  exact
    ⟨analyticReadUnary, sealReadUnary, witnessReadUnary, functionalReadUnary,
      finalReadUnary, routePkg, namePkg⟩

end BEDC.Derived.ZetaContinuationSocketUp
