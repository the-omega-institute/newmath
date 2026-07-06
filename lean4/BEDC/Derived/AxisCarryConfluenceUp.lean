import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AxisCarryConfluenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisCarryConfluenceCarrier [AskSetup] [PackageSetup]
    (u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory n ∧
    UnaryHistory routeLeft ∧
      UnaryHistory routeRight ∧
        UnaryHistory u ∧
          UnaryHistory v ∧
            UnaryHistory w ∧
              UnaryHistory valueLedger ∧
                UnaryHistory boundary ∧
                  UnaryHistory continuation ∧
                    UnaryHistory provenance ∧
                      UnaryHistory nameRow ∧
                        Cont u v routeLeft ∧
                          Cont u w routeRight ∧
                            Cont routeLeft routeRight valueLedger ∧
                              Cont boundary continuation provenance ∧
                                PkgSig bundle nameRow pkg ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row nameRow)
                                    (fun row : BHist =>
                                      hsame row routeLeft ∨ hsame row routeRight ∨
                                        hsame row valueLedger ∨ hsame row nameRow)
                                    (fun row : BHist =>
                                      PkgSig bundle nameRow pkg ∧ hsame row nameRow)
                                    hsame

theorem AxisCarryConfluenceCarrier_local_diamond [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      leftHandoff rightHandoff publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
      continuation provenance nameRow bundle pkg →
      Cont routeLeft n leftHandoff →
        Cont routeRight n rightHandoff →
          Cont leftHandoff rightHandoff publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory n ∧
                UnaryHistory leftHandoff ∧
                  UnaryHistory rightHandoff ∧
                    UnaryHistory publicRead ∧
                      Cont routeLeft n leftHandoff ∧
                        Cont routeRight n rightHandoff ∧
                          Cont leftHandoff rightHandoff publicRead ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute publicRoute publicPkg
  have nUnary : UnaryHistory n := carrier.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary nUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary nUnary rightRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed leftHandoffUnary rightHandoffUnary publicRoute
  exact
    ⟨nUnary, leftHandoffUnary, rightHandoffUnary, publicReadUnary, leftRoute,
      rightRoute, publicRoute, publicPkg⟩

theorem AxisCarryConfluenceCarrier_local_join_obligation [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      leftHandoff rightHandoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg ->
      Cont routeLeft n leftHandoff ->
        Cont routeRight n rightHandoff ->
          UnaryHistory n ∧
            UnaryHistory valueLedger ∧
              UnaryHistory leftHandoff ∧
                UnaryHistory rightHandoff ∧
                  Cont routeLeft n leftHandoff ∧
                    Cont routeRight n rightHandoff := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier leftRoute rightRoute
  have nUnary : UnaryHistory n := carrier.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.left
  have valueLedgerUnary : UnaryHistory valueLedger :=
    carrier.right.right.right.right.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary nUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary nUnary rightRoute
  exact
    ⟨nUnary, valueLedgerUnary, leftHandoffUnary, rightHandoffUnary, leftRoute,
      rightRoute⟩

theorem AxisCarryConfluenceCarrier_normalization_handoff [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      leftHandoff rightHandoff publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg →
      Cont routeLeft n leftHandoff →
        Cont routeRight n rightHandoff →
          Cont leftHandoff rightHandoff publicRead →
            Cont boundary publicRead boundaryRead →
              PkgSig bundle boundaryRead pkg →
                UnaryHistory boundaryRead ∧
                  Cont routeLeft n leftHandoff ∧
                    Cont routeRight n rightHandoff ∧
                      Cont leftHandoff rightHandoff publicRead ∧
                        Cont boundary publicRead boundaryRead ∧
                          PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute publicRoute boundaryRoute boundaryPkg
  have nUnary : UnaryHistory n := carrier.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.left
  have boundaryUnary : UnaryHistory boundary :=
    carrier.right.right.right.right.right.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary nUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary nUnary rightRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed leftHandoffUnary rightHandoffUnary publicRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary publicReadUnary boundaryRoute
  exact
    ⟨boundaryReadUnary, leftRoute, rightRoute, publicRoute, boundaryRoute, boundaryPkg⟩

theorem AxisCarryConfluenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
            continuation provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          hsame row routeLeft ∨ hsame row routeRight ∨ hsame row valueLedger ∨
            hsame row nameRow)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro nameRow ⟨carrier, hsame_refl nameRow⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.right))
    ledger_sound := by
      intro _row source
      exact ⟨carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
        source.right⟩
  }

theorem AxisCarryConfluenceCarrier_normal_form_obligation [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      leftHandoff rightHandoff normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg →
      Cont routeLeft n leftHandoff →
        Cont routeRight n rightHandoff →
          Cont leftHandoff rightHandoff normalRead →
            PkgSig bundle normalRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row n ∨ hsame row routeLeft ∨ hsame row routeRight ∨
                      hsame row valueLedger ∨ hsame row boundary ∨
                        hsame row continuation ∨ hsame row provenance ∨
                          hsame row nameRow ∨ hsame row normalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont routeLeft n leftHandoff ∧
                      Cont routeRight n rightHandoff ∧
                        Cont leftHandoff rightHandoff normalRead ∧
                          PkgSig bundle normalRead pkg)
                  hsame ∧
                UnaryHistory n ∧ UnaryHistory leftHandoff ∧
                  UnaryHistory rightHandoff ∧ UnaryHistory normalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier leftRoute rightRoute normalRoute normalPkg
  have nUnary : UnaryHistory n := carrier.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary nUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary nUnary rightRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed leftHandoffUnary rightHandoffUnary normalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row n ∨ hsame row routeLeft ∨ hsame row routeRight ∨
              hsame row valueLedger ∨ hsame row boundary ∨ hsame row continuation ∨
                hsame row provenance ∨ hsame row nameRow ∨ hsame row normalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont routeLeft n leftHandoff ∧
              Cont routeRight n rightHandoff ∧ Cont leftHandoff rightHandoff normalRead ∧
                PkgSig bundle normalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead ⟨hsame_refl normalRead, normalUnary⟩
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
          Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftRoute, rightRoute, normalRoute, normalPkg⟩
  }
  exact ⟨cert, nUnary, leftHandoffUnary, rightHandoffUnary, normalUnary⟩

theorem AxisCarryConfluenceCarrier_value_ledger_exhaustion [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg ->
      Cont valueLedger nameRow ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row valueLedger ∨ hsame row ledgerRead)
              (fun row : BHist =>
                hsame row routeLeft ∨ hsame row routeRight ∨ hsame row valueLedger ∨
                  hsame row boundary ∨ hsame row continuation ∨ hsame row provenance ∨
                    hsame row nameRow ∨ hsame row ledgerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont valueLedger nameRow ledgerRead ∧
                  PkgSig bundle ledgerRead pkg)
              hsame ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier ledgerRoute ledgerPkg
  have valueLedgerUnary : UnaryHistory valueLedger :=
    carrier.right.right.right.right.right.right.left
  have nameRowUnary : UnaryHistory nameRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed valueLedgerUnary nameRowUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row valueLedger ∨ hsame row ledgerRead)
          (fun row : BHist =>
            hsame row routeLeft ∨ hsame row routeRight ∨ hsame row valueLedger ∨
              hsame row boundary ∨ hsame row continuation ∨ hsame row provenance ∨
                hsame row nameRow ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont valueLedger nameRow ledgerRead ∧
              PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro valueLedger (Or.inl (hsame_refl valueLedger))
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
        | inl rowLedger =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowLedger)
        | inr rowRead =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) rowRead)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowLedger =>
          exact Or.inr (Or.inr (Or.inl rowLedger))
      | inr rowRead =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rowRead))))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowLedger =>
          exact
            ⟨unary_transport valueLedgerUnary (hsame_symm rowLedger), ledgerRoute, ledgerPkg⟩
      | inr rowRead =>
          exact
            ⟨unary_transport ledgerReadUnary (hsame_symm rowRead), ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, ledgerReadUnary⟩

theorem AxisCarryConfluenceCarrier_nonescape [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      escapeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg →
      Cont valueLedger boundary escapeRead →
        PkgSig bundle escapeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row routeLeft ∨ hsame row routeRight ∨ hsame row valueLedger ∨
                  hsame row boundary ∨ hsame row continuation ∨ hsame row provenance ∨
                    hsame row nameRow ∨ hsame row escapeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont valueLedger boundary escapeRead ∧
                  PkgSig bundle escapeRead pkg)
              hsame ∧ UnaryHistory escapeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier escapeRoute escapePkg
  have valueLedgerUnary : UnaryHistory valueLedger :=
    carrier.right.right.right.right.right.right.left
  have boundaryUnary : UnaryHistory boundary :=
    carrier.right.right.right.right.right.right.right.left
  have escapeUnary : UnaryHistory escapeRead :=
    unary_cont_closed valueLedgerUnary boundaryUnary escapeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row routeLeft ∨ hsame row routeRight ∨ hsame row valueLedger ∨
              hsame row boundary ∨ hsame row continuation ∨ hsame row provenance ∨
                hsame row nameRow ∨ hsame row escapeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont valueLedger boundary escapeRead ∧
              PkgSig bundle escapeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro escapeRead
        ⟨hsame_refl escapeRead, escapeUnary⟩
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
      exact ⟨source.right, escapeRoute, escapePkg⟩
  }
  exact ⟨cert, escapeUnary⟩

theorem AxisCarryConfluenceCarrier_obligation [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
        continuation provenance nameRow bundle pkg →
      UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory w ∧ UnaryHistory n ∧
        UnaryHistory routeLeft ∧ UnaryHistory routeRight ∧ UnaryHistory valueLedger ∧
          UnaryHistory boundary ∧ UnaryHistory continuation ∧
            UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont u v routeLeft ∧
              Cont u w routeRight ∧ Cont routeLeft routeRight valueLedger ∧
                Cont boundary continuation provenance ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig SemanticNameCert
  intro carrier
  obtain ⟨nUnary, routeLeftUnary, routeRightUnary, uUnary, vUnary, wUnary,
    valueLedgerUnary, boundaryUnary, continuationUnary, provenanceUnary, nameRowUnary,
    leftRoute, rightRoute, ledgerRoute, boundaryRoute, pkgRow, _cert⟩ := carrier
  exact
    ⟨uUnary, vUnary, wUnary, nUnary, routeLeftUnary, routeRightUnary, valueLedgerUnary,
      boundaryUnary, continuationUnary, provenanceUnary, nameRowUnary, leftRoute,
      rightRoute, ledgerRoute, boundaryRoute, pkgRow⟩

end BEDC.Derived.AxisCarryConfluenceUp
