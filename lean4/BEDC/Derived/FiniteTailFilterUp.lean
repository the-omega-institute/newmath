import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteTailFilterCarrier (S D R B Q E H _C _P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory S /\ UnaryHistory D /\ UnaryHistory B /\ UnaryHistory E /\ UnaryHistory H /\
    Cont S D R /\ Cont R B Q /\ hsame N E

theorem FiniteTailFilterCarrier_tail_window_exactness
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        PkgSig bundle sealRow pkg ->
          UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory Q /\
            UnaryHistory E /\ UnaryHistory sealRow /\ Cont S D R /\ Cont R B Q /\
              Cont Q E sealRow /\ hsame N E /\ PkgSig bundle sealRow pkg /\
                SemanticNameCert
                  (fun row : BHist => hsame row sealRow /\ UnaryHistory row)
                  (fun row : BHist => Cont Q E row /\ Cont S D R /\ Cont R B Q)
                  (fun row : BHist => hsame row sealRow /\ PkgSig bundle sealRow pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sealRoute sealPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRow /\ UnaryHistory row)
        (fun row : BHist => Cont Q E row /\ Cont S D R /\ Cont R B Q)
        (fun row : BHist => hsame row sealRow /\ PkgSig bundle sealRow pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRow (And.intro (hsame_refl sealRow) unarySeal)
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro row source
        exact
          ⟨cont_result_hsame_transport sealRoute (hsame_symm source.left),
            routeR, routeQ⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left sealPkg
    }
  exact
    ⟨unaryS, unaryD, unaryR, unaryQ, unaryE, unarySeal, routeR, routeQ, sealRoute,
      sameNameSeal, sealPkg, cert⟩

theorem FiniteTailFilterCarrier_real_seal_handoff
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        UnaryHistory H ->
          Cont sealRow H realRead ->
            UnaryHistory C ->
              Cont realRead C completionRead ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory B /\
                    UnaryHistory Q /\ UnaryHistory E /\ UnaryHistory sealRow /\
                      UnaryHistory realRead /\ UnaryHistory completionRead /\ Cont S D R /\
                        Cont R B Q /\ Cont Q E sealRow /\ Cont sealRow H realRead /\
                          Cont realRead C completionRead /\ hsame N E /\
                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute unaryH realRoute unaryC completionRoute completionPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryCarrierH, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealRead : UnaryHistory realRead :=
    unary_cont_closed unarySeal unaryH realRoute
  have unaryCompletionRead : UnaryHistory completionRead :=
    unary_cont_closed unaryRealRead unaryC completionRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unarySeal, unaryRealRead,
      unaryCompletionRead, routeR, routeQ, sealRoute, realRoute, completionRoute,
      sameNameSeal, completionPkg⟩

theorem FiniteTailFilterCarrier_cofinal_route_exhaustion
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          UnaryHistory C ->
            Cont realWindowRead C completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                  UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                    UnaryHistory sealRead ∧ UnaryHistory realWindowRead ∧
                      UnaryHistory completionRead ∧ Cont S D R ∧ Cont R B Q ∧
                        Cont Q E sealRead ∧ Cont sealRead H realWindowRead ∧
                          Cont realWindowRead C completionRead ∧ hsame N E ∧
                            PkgSig bundle completionRead pkg ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row completionRead ∧
                                  UnaryHistory row)
                                (fun row : BHist => hsame row completionRead ∧
                                  Cont Q E sealRead ∧ Cont sealRead H realWindowRead ∧
                                    Cont realWindowRead C completionRead)
                                (fun row : BHist => hsame row completionRead ∧
                                  PkgSig bundle completionRead pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sealRoute realWindowRoute unaryC completionRoute completionPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unaryRealWindow unaryC completionRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row completionRead ∧ Cont Q E sealRead ∧
          Cont sealRead H realWindowRead ∧ Cont realWindowRead C completionRead)
        (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro completionRead ⟨hsame_refl completionRead, unaryCompletion⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, sealRoute, realWindowRoute, completionRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, completionPkg⟩
    }
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryCompletion, routeR, routeQ, sealRoute, realWindowRoute,
      completionRoute, sameNameSeal, completionPkg, cert⟩

theorem FiniteTailFilterCarrier_real_window_consumer
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realWindowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H realWindowRead ->
          PkgSig bundle realWindowRead pkg ->
            UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory B /\
              UnaryHistory Q /\ UnaryHistory E /\ UnaryHistory sealRow /\
                UnaryHistory realWindowRead /\ Cont S D R /\ Cont R B Q /\
                  Cont Q E sealRow /\ Cont sealRow H realWindowRead /\ hsame N E /\
                    PkgSig bundle realWindowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute realWindowRoute realWindowPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unarySeal, unaryRealWindow,
      routeR, routeQ, sealRoute, realWindowRoute, sameNameSeal, realWindowPkg⟩

theorem FiniteTailFilterCarrier_cofinal_window_directedness_obligation
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      UnaryHistory C ->
        Cont Q E sealRow ->
          Cont sealRow C replayRead ->
            PkgSig bundle replayRead pkg ->
              UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory B /\
                UnaryHistory Q /\ UnaryHistory E /\ UnaryHistory sealRow /\
                  UnaryHistory replayRead /\ Cont S D R /\ Cont R B Q /\
                    Cont Q E sealRow /\ Cont sealRow C replayRead /\ hsame N E /\
                      PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier unaryC sealRoute replayRoute replayPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryReplay : UnaryHistory replayRead :=
    unary_cont_closed unarySeal unaryC replayRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unarySeal, unaryReplay, routeR,
      routeQ, sealRoute, replayRoute, sameNameSeal, replayPkg⟩

theorem FiniteTailFilterCarrier_terminal_cofinal_consumer_exclusion
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow replayRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      UnaryHistory C ->
        Cont Q E sealRow ->
          Cont sealRow C replayRead ->
            Cont replayRead H terminalRead ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory B /\
                  UnaryHistory Q /\ UnaryHistory E /\ UnaryHistory sealRow /\
                    UnaryHistory replayRead /\ UnaryHistory terminalRead /\ Cont S D R /\
                      Cont R B Q /\ Cont Q E sealRow /\ Cont sealRow C replayRead /\
                        Cont replayRead H terminalRead /\ hsame N E /\
                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier unaryC sealRoute replayRoute terminalRoute terminalPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R := unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q := unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow := unary_cont_closed unaryQ unaryE sealRoute
  have unaryReplay : UnaryHistory replayRead :=
    unary_cont_closed unarySeal unaryC replayRoute
  have unaryTerminal : UnaryHistory terminalRead :=
    unary_cont_closed unaryReplay unaryH terminalRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unarySeal, unaryReplay,
      unaryTerminal, routeR, routeQ, sealRoute, replayRoute, terminalRoute,
      sameNameSeal, terminalPkg⟩

theorem FiniteTailFilterCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      PkgSig bundle E pkg ->
        UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
          UnaryHistory Q ∧ UnaryHistory E ∧ Cont S D R ∧ Cont R B Q ∧ hsame N E ∧
            PkgSig bundle E pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row E ∧ UnaryHistory row)
                (fun row : BHist => hsame row E)
                (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have sourceE : (fun row : BHist => hsame row E ∧ UnaryHistory row) E := by
    exact ⟨hsame_refl E, unaryE⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row E ∧ UnaryHistory row)
        (fun row : BHist => hsame row E)
        (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro E sourceE
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
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, routeR, routeQ, sameNameSeal,
      pkgSig, cert⟩

theorem FiniteTailFilterCarrier_transport_obligation
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N S' D' R' B' Q' E' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      hsame S S' -> hsame D D' -> hsame R R' -> hsame B B' ->
        hsame Q Q' -> hsame E E' -> hsame N N' ->
          PkgSig bundle E' pkg ->
            FiniteTailFilterCarrier S' D' R' B' Q' E' H C P N' /\
              UnaryHistory S' /\ UnaryHistory D' /\ UnaryHistory R' /\
                UnaryHistory B' /\ UnaryHistory Q' /\ UnaryHistory E' /\
                  Cont S' D' R' /\ Cont R' B' Q' /\ hsame N' E' /\
                    PkgSig bundle E' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameS sameD sameR sameB sameQ sameE sameN pkgSig
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryS' : UnaryHistory S' := unary_transport unaryS sameS
  have unaryD' : UnaryHistory D' := unary_transport unaryD sameD
  have unaryB' : UnaryHistory B' := unary_transport unaryB sameB
  have unaryE' : UnaryHistory E' := unary_transport unaryE sameE
  have routeR' : Cont S' D' R' :=
    cont_hsame_transport sameS sameD sameR routeR
  have routeQ' : Cont R' B' Q' :=
    cont_hsame_transport sameR sameB sameQ routeQ
  have unaryR' : UnaryHistory R' :=
    unary_cont_closed unaryS' unaryD' routeR'
  have unaryQ' : UnaryHistory Q' :=
    unary_cont_closed unaryR' unaryB' routeQ'
  have sameNameSeal' : hsame N' E' :=
    hsame_trans (hsame_symm sameN) (hsame_trans sameNameSeal sameE)
  exact
    ⟨⟨unaryS', unaryD', unaryB', unaryE', unaryH, routeR', routeQ',
        sameNameSeal'⟩,
      unaryS', unaryD', unaryR', unaryB', unaryQ', unaryE', routeR', routeQ',
      sameNameSeal', pkgSig⟩

theorem FiniteTailFilterCarrier_real_completion_lattice_link
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N cofinalWindow latticeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D cofinalWindow ->
        Cont cofinalWindow E latticeRead ->
          PkgSig bundle latticeRead pkg ->
            UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
              UnaryHistory cofinalWindow ∧ UnaryHistory latticeRead ∧ Cont S D R ∧
                Cont S D cofinalWindow ∧ Cont cofinalWindow E latticeRead ∧
                  hsame cofinalWindow R ∧ hsame N E ∧
                    PkgSig bundle latticeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier cofinalRoute latticeRoute latticePkg
  obtain ⟨unaryS, unaryD, _unaryB, unaryE, _unaryH, routeR, _routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryCofinalWindow : UnaryHistory cofinalWindow :=
    unary_cont_closed unaryS unaryD cofinalRoute
  have unaryLatticeRead : UnaryHistory latticeRead :=
    unary_cont_closed unaryCofinalWindow unaryE latticeRoute
  have cofinalWindowSameR : hsame cofinalWindow R :=
    cont_deterministic cofinalRoute routeR
  exact
    ⟨unaryS, unaryD, unaryR, unaryE, unaryCofinalWindow, unaryLatticeRead, routeR,
      cofinalRoute, latticeRoute, cofinalWindowSameR, sameNameSeal, latticePkg⟩

theorem FiniteTailFilterCarrier_structural_provenance_obligation
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      UnaryHistory P ->
        Cont P N E ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row N /\ UnaryHistory row)
                (fun row : BHist => Cont P row E /\ hsame N E)
                (fun row : BHist => hsame row N /\ PkgSig bundle P pkg)
                hsame /\
              UnaryHistory P /\ UnaryHistory N /\ hsame N E /\ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryP provenanceRoute provenancePkg
  obtain ⟨_unaryS, _unaryD, _unaryB, unaryE, _unaryH, _routeR, _routeQ,
    sameNameSeal⟩ := carrier
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N /\ UnaryHistory row)
        (fun row : BHist => Cont P row E /\ hsame N E)
        (fun row : BHist => hsame row N /\ PkgSig bundle P pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        cases source.left
        exact ⟨provenanceRoute, sameNameSeal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact ⟨cert, unaryP, unaryN, sameNameSeal, provenancePkg⟩

theorem FiniteTailFilterCarrier_shared_window_meet
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N meetWindow siblingRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont S D meetWindow →
        Cont meetWindow E siblingRead →
          Cont siblingRead H realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                UnaryHistory meetWindow ∧ UnaryHistory siblingRead ∧ UnaryHistory realRead ∧
                  Cont S D R ∧ Cont S D meetWindow ∧ Cont meetWindow E siblingRead ∧
                    Cont siblingRead H realRead ∧ hsame meetWindow R ∧ hsame N E ∧
                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier meetRoute siblingRoute realRoute realPkg
  obtain ⟨unaryS, unaryD, _unaryB, unaryE, unaryH, routeR, _routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryMeet : UnaryHistory meetWindow :=
    unary_cont_closed unaryS unaryD meetRoute
  have unarySibling : UnaryHistory siblingRead :=
    unary_cont_closed unaryMeet unaryE siblingRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unarySibling unaryH realRoute
  have sameMeet : hsame meetWindow R :=
    cont_deterministic meetRoute routeR
  exact
    ⟨unaryS, unaryD, unaryR, unaryE, unaryMeet, unarySibling, unaryReal, routeR,
      meetRoute, siblingRoute, realRoute, sameMeet, sameNameSeal, realPkg⟩

theorem FiniteTailFilterCarrier_nonescape
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N S' D' R' B' Q' E' H' C' P' N' : BHist} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      FiniteTailFilterCarrier S' D' R' B' Q' E' H' C' P' N' →
        hsame S S' → hsame D D' → hsame B B' → hsame E E' →
          hsame R R' ∧ hsame Q Q' ∧ hsame N N' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier carrier' sameS sameD sameB sameE
  obtain ⟨_unaryS, _unaryD, _unaryB, _unaryE, _unaryH, routeR, routeQ,
    sameNameSeal⟩ := carrier
  obtain ⟨_unaryS', _unaryD', _unaryB', _unaryE', _unaryH', routeR', routeQ',
    sameNameSeal'⟩ := carrier'
  have sameR : hsame R R' :=
    cont_respects_hsame sameS sameD routeR routeR'
  have sameQ : hsame Q Q' :=
    cont_respects_hsame sameR sameB routeQ routeQ'
  have sameN : hsame N N' :=
    hsame_trans sameNameSeal
      (hsame_trans sameE (hsame_symm sameNameSeal'))
  exact ⟨sameR, sameQ, sameN⟩

theorem FiniteTailFilterCarrier_common_tail_seal_cofinality
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realWindowRead uniformRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H realWindowRead ->
          Cont realWindowRead C uniformRead ->
            Cont uniformRead H terminalRead ->
              UnaryHistory C ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory S /\ UnaryHistory D /\ UnaryHistory R /\ UnaryHistory B /\
                    UnaryHistory Q /\ UnaryHistory E /\ UnaryHistory H /\ UnaryHistory C /\
                      UnaryHistory sealRow /\ UnaryHistory realWindowRead /\
                        UnaryHistory uniformRead /\ UnaryHistory terminalRead /\
                          Cont S D R /\ Cont R B Q /\ Cont Q E sealRow /\
                            Cont sealRow H realWindowRead /\
                              Cont realWindowRead C uniformRead /\
                                Cont uniformRead H terminalRead /\ hsame N E /\
                                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute realWindowRoute uniformRoute terminalRoute unaryC terminalPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, routeR, routeQ, sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryUniform : UnaryHistory uniformRead :=
    unary_cont_closed unaryRealWindow unaryC uniformRoute
  have unaryTerminal : UnaryHistory terminalRead :=
    unary_cont_closed unaryUniform unaryH terminalRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryUniform, unaryTerminal, routeR, routeQ, sealRoute,
      realWindowRoute, uniformRoute, terminalRoute, sameNameSeal, terminalPkg⟩

end BEDC.Derived.FiniteTailFilterUp
