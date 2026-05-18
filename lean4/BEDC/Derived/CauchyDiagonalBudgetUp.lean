import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyDiagonalBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyDiagonalBudgetCarrier [AskSetup] [PackageSetup]
    (epsilon m w d k s h c p name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
    UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory name ∧ Cont epsilon m w ∧ Cont w d k ∧
        Cont k s h ∧ Cont h c p ∧ Cont c p name ∧ PkgSig bundle p pkg

theorem CauchyDiagonalBudgetCarrier_selection_determinacy [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name route sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont epsilon m route →
        Cont k s sealRow →
          PkgSig bundle sealRow pkg →
            UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
              UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory route ∧ UnaryHistory sealRow ∧
                Cont epsilon m route ∧ Cont k s sealRow ∧ PkgSig bundle sealRow pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row p ∧ UnaryHistory row)
                    (fun row : BHist => hsame row p)
                    (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                    hsame := by
  intro carrier routeRow sealRoute sealPkg
  have epsilonUnary : UnaryHistory epsilon := carrier.left
  have mUnary : UnaryHistory m := carrier.right.left
  have wUnary : UnaryHistory w := carrier.right.right.left
  have dUnary : UnaryHistory d := carrier.right.right.right.left
  have kUnary : UnaryHistory k := carrier.right.right.right.right.left
  have sUnary : UnaryHistory s := carrier.right.right.right.right.right.left
  have pUnary : UnaryHistory p :=
    carrier.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have routeUnary : UnaryHistory route :=
    unary_cont_closed epsilonUnary mUnary routeRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed kUnary sUnary sealRoute
  have sourceP :
      (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact ⟨hsame_refl p, pUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro p sourceP
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same source
        have sameRow' : hsame row' p :=
          hsame_trans (hsame_symm same) source.left
        exact ⟨sameRow', unary_transport source.right same⟩
    }
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact source.left
      ledger_sound := by
        intro row source
        exact ⟨source.left, pPkg⟩
    }
  exact
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, routeUnary, sealUnary,
      routeRow, sealRoute, sealPkg, cert⟩

theorem CauchyDiagonalBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
        UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧
          UnaryHistory p ∧ UnaryHistory name ∧ Cont epsilon m w ∧ Cont w d k ∧
            Cont k s h ∧ Cont h c p ∧ Cont c p name ∧ PkgSig bundle p pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row p ∧ UnaryHistory row)
                (fun row : BHist => hsame row p)
                (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
  refine
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg, ?_⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro p (And.intro (hsame_refl p) pUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact And.intro source.left pPkg
  }

theorem CauchyDiagonalBudgetCarrier_classifier_stability [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      hsame p transported →
        PkgSig bundle transported pkg →
          SemanticNameCert
            (fun row : BHist =>
              CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
                hsame row transported)
            (fun row : BHist => hsame row transported ∧ UnaryHistory row)
            (fun row : BHist =>
              PkgSig bundle p pkg ∧ PkgSig bundle transported pkg ∧
                hsame row transported)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier pTransported transportedPkg
  have pUnary : UnaryHistory p :=
    carrier.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro transported (And.intro carrier (hsame_refl transported))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left
          (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      have pRow : hsame p row :=
        hsame_trans pTransported (hsame_symm source.right)
      exact And.intro source.right (unary_transport pUnary pRow)
    ledger_sound := by
      intro row source
      exact And.intro pPkg (And.intro transportedPkg source.right)
  }

theorem CauchyDiagonalBudget_route_factorization [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
                hsame row endpoint)
            (fun _row : BHist =>
              Cont epsilon m w ∧ Cont w d k ∧ Cont k s h ∧ Cont h c endpoint ∧
                PkgSig bundle endpoint pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier endpointRoute endpointPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, _hCP, cPName, pPkg⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro
          ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
            nameUnary, epsilonMW, wDK, kSH, _hCP, cPName, pPkg⟩
          (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨epsilonMW, wDK, kSH, endpointRoute, endpointPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport endpointUnary (hsame_symm source.right), endpointPkg⟩
  }

theorem CauchyDiagonalBudgetCarrier_real_completeness_handoff [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont k s sealEndpoint →
        PkgSig bundle sealEndpoint pkg →
          SemanticNameCert
            (fun row : BHist =>
              CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
                hsame row sealEndpoint)
            (fun _row : BHist => Cont epsilon m w ∧ Cont w d k ∧ Cont k s sealEndpoint)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealEndpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
  have sealUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed kUnary sUnary sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealEndpoint (And.intro
          ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
            nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
          (hsame_refl sealEndpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨epsilonMW, wDK, sealRoute⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport sealUnary (hsame_symm source.right), sealPkg⟩
  }

theorem CauchyDiagonalBudgetCarrier_real_seal_scope [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name sealEndpoint boundary realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont k s sealEndpoint ->
        Cont h c boundary ->
          Cont sealEndpoint boundary realRead ->
            PkgSig bundle boundary pkg ->
              PkgSig bundle realRead pkg ->
                UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
                  UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧
                    UnaryHistory sealEndpoint ∧ UnaryHistory boundary ∧
                      UnaryHistory realRead ∧ Cont epsilon m w ∧ Cont w d k ∧
                        Cont k s sealEndpoint ∧ Cont h c boundary ∧
                          Cont sealEndpoint boundary realRead ∧ PkgSig bundle p pkg ∧
                            PkgSig bundle boundary pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealRoute boundaryRoute realRoute boundaryPkg realPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, _pUnary,
      _nameUnary, epsilonMW, wDK, _kSH, _hCP, _cPName, pPkg⟩
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed kUnary sUnary sealRoute
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed hUnary cUnary boundaryRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealEndpointUnary boundaryUnary realRoute
  exact
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary,
      sealEndpointUnary, boundaryUnary, realReadUnary, epsilonMW, wDK, sealRoute,
      boundaryRoute, realRoute, pPkg, boundaryPkg, realPkg⟩

theorem CauchyDiagonalBudgetCarrier_transported_selector_naturality [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name epsilon' m' w' d' k' s' h' c' p' name' route route'
      sealRow sealRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      CauchyDiagonalBudgetCarrier epsilon' m' w' d' k' s' h' c' p' name' bundle pkg →
        hsame epsilon epsilon' →
          hsame m m' →
            hsame k k' →
              hsame s s' →
                Cont epsilon m route →
                  Cont epsilon' m' route' →
                    Cont k s sealRow →
                      Cont k' s' sealRow' →
                        hsame route route' ∧ hsame sealRow sealRow' ∧
                          UnaryHistory route' ∧ UnaryHistory sealRow' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier transported sameEpsilon sameM sameK sameS routeStep transportedRoute sealStep
    transportedSeal
  obtain ⟨epsilonUnary, mUnary, _wUnary, _dUnary, kUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nameUnary, _epsilonMW, _wDK, _kSH, _hCP, _cPName, _pPkg⟩ := carrier
  obtain ⟨epsilonUnary', mUnary', _wUnary', _dUnary', kUnary', sUnary', _hUnary', _cUnary',
    _pUnary', _nameUnary', _epsilonMW', _wDK', _kSH', _hCP', _cPName', _pPkg'⟩ :=
      transported
  have routeSame : hsame route route' :=
    cont_respects_hsame sameEpsilon sameM routeStep transportedRoute
  have sealSame : hsame sealRow sealRow' :=
    cont_respects_hsame sameK sameS sealStep transportedSeal
  have transportedRouteUnary : UnaryHistory route' :=
    unary_cont_closed epsilonUnary' mUnary' transportedRoute
  have transportedSealUnary : UnaryHistory sealRow' :=
    unary_cont_closed kUnary' sUnary' transportedSeal
  exact ⟨routeSame, sealSame, transportedRouteUnary, transportedSealUnary⟩

theorem CauchyDiagonalBudget_mesh_comparison_exactness [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ∧
            hsame row k)
        (fun _row : BHist => Cont epsilon m w ∧ Cont w d k ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
      nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro k (And.intro
          ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, pUnary,
            nameUnary, epsilonMW, wDK, kSH, hCP, cPName, pPkg⟩
          (hsame_refl k))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨epsilonMW, wDK, pPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport kUnary (hsame_symm source.right), pPkg⟩
  }

theorem CauchyDiagonalBudgetCarrier_seal_boundary_factorization [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name sealEndpoint boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont k s sealEndpoint →
        Cont h c boundary →
          PkgSig bundle boundary pkg →
            UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
              UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory sealEndpoint ∧
                UnaryHistory boundary ∧ Cont epsilon m w ∧ Cont w d k ∧
                  Cont k s sealEndpoint ∧ Cont h c boundary ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier sealRoute boundaryRoute boundaryPkg
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, cUnary, _pUnary,
      _nameUnary, epsilonMW, wDK, _kSH, _hCP, _cPName, pPkg⟩
  have sealUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed kUnary sUnary sealRoute
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed hUnary cUnary boundaryRoute
  exact
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, sealUnary, boundaryUnary,
      epsilonMW, wDK, sealRoute, boundaryRoute, pPkg, boundaryPkg⟩

theorem CauchyDiagonalBudgetCarrier_seal_consumer_coverage [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name route sealRow finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg →
      Cont epsilon m route →
        Cont k s sealRow →
          Cont sealRow h finalRead →
            UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
              UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory route ∧
                UnaryHistory sealRow ∧ UnaryHistory finalRead ∧ Cont epsilon m route ∧
                  Cont k s sealRow ∧ Cont sealRow h finalRead ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier routeStep sealRoute finalRoute
  rcases carrier with
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, _cUnary, _pUnary,
      _nameUnary, _epsilonMW, _wDK, _kSH, _hCP, _cPName, pPkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed epsilonUnary mUnary routeStep
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed kUnary sUnary sealRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed sealUnary hUnary finalRoute
  exact
    ⟨epsilonUnary, mUnary, wUnary, dUnary, kUnary, sUnary, hUnary, routeUnary, sealUnary,
      finalUnary, routeStep, sealRoute, finalRoute, pPkg⟩

theorem CauchyDiagonalBudgetCarrier_route_determinacy [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name route0 route1 dyadic0 dyadic1 compare0 compare1 seal0
      seal1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont epsilon m route0 ->
        Cont epsilon m route1 ->
          Cont route0 d dyadic0 ->
            Cont route1 d dyadic1 ->
              Cont dyadic0 k compare0 ->
                Cont dyadic1 k compare1 ->
                  Cont compare0 s seal0 ->
                    Cont compare1 s seal1 ->
                      PkgSig bundle seal0 pkg ->
                        PkgSig bundle seal1 pkg ->
                          hsame route0 route1 ∧ hsame dyadic0 dyadic1 ∧
                            hsame compare0 compare1 ∧ hsame seal0 seal1 ∧
                              UnaryHistory seal0 ∧ UnaryHistory seal1 ∧
                                PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier routeStep0 routeStep1 routeDyadic0 routeDyadic1 dyadicCompare0
    dyadicCompare1 compareSeal0 compareSeal1 _sealPkg0 _sealPkg1
  obtain ⟨epsilonUnary, mUnary, _wUnary, dUnary, kUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nameUnary, _epsilonMW, _wDK, _kSH, _hCP, _cPName, pPkg⟩ := carrier
  have routeSame : hsame route0 route1 :=
    cont_deterministic routeStep0 routeStep1
  have routeUnary0 : UnaryHistory route0 :=
    unary_cont_closed epsilonUnary mUnary routeStep0
  have routeUnary1 : UnaryHistory route1 :=
    unary_cont_closed epsilonUnary mUnary routeStep1
  have dyadicSame : hsame dyadic0 dyadic1 :=
    cont_respects_hsame routeSame (hsame_refl d) routeDyadic0 routeDyadic1
  have dyadicUnary0 : UnaryHistory dyadic0 :=
    unary_cont_closed routeUnary0 dUnary routeDyadic0
  have dyadicUnary1 : UnaryHistory dyadic1 :=
    unary_cont_closed routeUnary1 dUnary routeDyadic1
  have compareSame : hsame compare0 compare1 :=
    cont_respects_hsame dyadicSame (hsame_refl k) dyadicCompare0 dyadicCompare1
  have compareUnary0 : UnaryHistory compare0 :=
    unary_cont_closed dyadicUnary0 kUnary dyadicCompare0
  have compareUnary1 : UnaryHistory compare1 :=
    unary_cont_closed dyadicUnary1 kUnary dyadicCompare1
  have sealSame : hsame seal0 seal1 :=
    cont_respects_hsame compareSame (hsame_refl s) compareSeal0 compareSeal1
  have sealUnary0 : UnaryHistory seal0 :=
    unary_cont_closed compareUnary0 sUnary compareSeal0
  have sealUnary1 : UnaryHistory seal1 :=
    unary_cont_closed compareUnary1 sUnary compareSeal1
  exact ⟨routeSame, dyadicSame, compareSame, sealSame, sealUnary0, sealUnary1, pPkg⟩

theorem CauchyDiagonalBudgetCarrier_regseq_real_route_lock [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name window comparison sealRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont epsilon m window -> Cont window d comparison -> Cont comparison s sealRead ->
        Cont h c boundary -> PkgSig bundle boundary pkg ->
          hsame w window ∧ hsame k comparison ∧ hsame h sealRead ∧ UnaryHistory window ∧
            UnaryHistory comparison ∧ UnaryHistory sealRead ∧ UnaryHistory boundary ∧
              PkgSig bundle p pkg ∧ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier epsilonMWindow windowDComparison comparisonSSeal hCBoundary boundaryPkg
  obtain ⟨epsilonUnary, mUnary, _wUnary, dUnary, _kUnary, sUnary, hUnary, cUnary,
    _pUnary, _nameUnary, epsilonMW, wDK, kSH, _hCP, _cPName, pPkg⟩ := carrier
  have sameWindow : hsame w window := cont_deterministic epsilonMW epsilonMWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed (unary_cont_closed epsilonUnary mUnary epsilonMWindow) dUnary
      windowDComparison
  have sameComparison : hsame k comparison :=
    cont_respects_hsame sameWindow (hsame_refl d) wDK windowDComparison
  have sealUnary : UnaryHistory sealRead := unary_cont_closed comparisonUnary sUnary comparisonSSeal
  exact ⟨sameWindow, sameComparison,
    cont_respects_hsame sameComparison (hsame_refl s) kSH comparisonSSeal,
    unary_cont_closed epsilonUnary mUnary epsilonMWindow, comparisonUnary, sealUnary,
    unary_cont_closed hUnary cUnary hCBoundary, pPkg, boundaryPkg⟩

theorem CauchyDiagonalBudgetCarrier_nonescape [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name externalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont h c externalRead -> PkgSig bundle p pkg ->
        UnaryHistory epsilon ∧ UnaryHistory m ∧ UnaryHistory w ∧ UnaryHistory d ∧
          UnaryHistory k ∧ UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧
            UnaryHistory p ∧ UnaryHistory name ∧ UnaryHistory externalRead ∧
              Cont h c externalRead ∧ PkgSig bundle p pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row p ∧ UnaryHistory row)
                  (fun row : BHist => hsame row p)
                  (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier externalRoute pPkg
  rcases CauchyDiagonalBudgetCarrier_namecert_obligations carrier with
    ⟨epsilonU, mU, wU, dU, kU, sU, hU, cU, pU, nameU, _epsilonMW, _wDK, _kSH,
      _hCP, _cPName, _carrierPkg, cert⟩
  exact
    ⟨epsilonU, mU, wU, dU, kU, sU, hU, cU, pU, nameU,
      unary_cont_closed hU cU externalRoute, externalRoute, pPkg, cert⟩

theorem CauchyDiagonalBudgetCarrier_finite_approximation_handoff [AskSetup] [PackageSetup]
    {epsilon m w d k s h c p name window comparison sealRead finiteApprox : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDiagonalBudgetCarrier epsilon m w d k s h c p name bundle pkg ->
      Cont epsilon m window ->
        Cont window d comparison ->
          Cont comparison s sealRead ->
            Cont sealRead h finiteApprox ->
              PkgSig bundle finiteApprox pkg ->
                hsame w window ∧ hsame k comparison ∧ hsame h sealRead ∧
                  UnaryHistory window ∧ UnaryHistory comparison ∧ UnaryHistory sealRead ∧
                    UnaryHistory finiteApprox ∧ PkgSig bundle p pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row finiteApprox ∧ UnaryHistory row)
                        (fun row : BHist => hsame row finiteApprox)
                        (fun row : BHist =>
                          hsame row finiteApprox ∧ PkgSig bundle finiteApprox pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier epsilonMWindow windowDComparison comparisonSSeal sealFinite finitePkg
  obtain ⟨epsilonUnary, mUnary, _wUnary, dUnary, _kUnary, sUnary, hUnary, _cUnary,
    _pUnary, _nameUnary, epsilonMW, wDK, kSH, _hCP, _cPName, pPkg⟩ := carrier
  have sameWindow : hsame w window :=
    cont_deterministic epsilonMW epsilonMWindow
  have windowUnary : UnaryHistory window :=
    unary_cont_closed epsilonUnary mUnary epsilonMWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed windowUnary dUnary windowDComparison
  have sameComparison : hsame k comparison :=
    cont_respects_hsame sameWindow (hsame_refl d) wDK windowDComparison
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed comparisonUnary sUnary comparisonSSeal
  have sameSeal : hsame h sealRead :=
    cont_respects_hsame sameComparison (hsame_refl s) kSH comparisonSSeal
  have finiteUnary : UnaryHistory finiteApprox :=
    unary_cont_closed sealUnary hUnary sealFinite
  have sourceFinite :
      (fun row : BHist => hsame row finiteApprox ∧ UnaryHistory row) finiteApprox := by
    exact ⟨hsame_refl finiteApprox, finiteUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row finiteApprox ∧ UnaryHistory row)
        (fun row : BHist => hsame row finiteApprox)
        (fun row : BHist => hsame row finiteApprox ∧ PkgSig bundle finiteApprox pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro finiteApprox sourceFinite
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left finitePkg
    }
  exact
    ⟨sameWindow, sameComparison, sameSeal, windowUnary, comparisonUnary, sealUnary,
      finiteUnary, pPkg, cert⟩

end BEDC.Derived.CauchyDiagonalBudgetUp
