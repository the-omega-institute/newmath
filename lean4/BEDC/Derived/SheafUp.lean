import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.TopologyUp

def SheafBHistPointGermLedger
    (point openHist sectionHist germ : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory openHist ∧ Cont openHist sectionHist germ

def SheafBHistPointGermComparison
    (point openA sectA germA openB sectB germB common : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory openA ∧ UnaryHistory openB ∧ UnaryHistory common ∧
    hsame common openA ∧ hsame common openB ∧ Cont common sectA germA ∧
      Cont common sectB germB ∧ hsame germA germB

def SheafConsumerAccessTrace (root : BHist) (trace : List BHist) : Prop :=
  UnaryHistory root ∧ ∀ row : BHist, List.Mem row trace -> UnaryHistory row

theorem SheafConsumerAccessTrace_append_closed {root : BHist} {left right : List BHist} :
    SheafConsumerAccessTrace root left -> SheafConsumerAccessTrace root right ->
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right) := by
  induction left with
  | nil =>
      intro leftTrace rightTrace
      exact And.intro leftTrace.left
        (And.intro leftTrace.left
          (by
            intro row rowMem
            exact rightTrace.right row rowMem))
  | cons head tail ih =>
      intro leftTrace rightTrace
      have tailTrace : SheafConsumerAccessTrace root tail :=
        And.intro leftTrace.left
          (by
            intro row rowMem
            exact leftTrace.right row (List.Mem.tail head rowMem))
      have appendedTail :
          UnaryHistory root ∧ SheafConsumerAccessTrace root (tail ++ right) :=
        ih tailTrace rightTrace
      exact And.intro leftTrace.left
        (And.intro leftTrace.left
          (by
            intro row rowMem
            cases rowMem with
            | head =>
                exact leftTrace.right head (List.Mem.head tail)
            | tail _ tailMem =>
                exact appendedTail.right.right row tailMem))

def SheafBHistCoverNerveLedger
    (ambient member overlap route germ : BHist) : Prop :=
  UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧ hsame overlap member ∧
    Cont overlap route germ

theorem SheafBHistCoverNerveLedger_empty_boundary
    {ambient member overlap route germ : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame germ BHist.Empty -> hsame overlap BHist.Empty ∧ hsame route BHist.Empty := by
  intro ledger germEmpty
  have appendEmpty : append overlap route = BHist.Empty :=
    ledger.right.right.right.right.symm.trans germEmpty
  exact append_eq_empty_iff.mp appendEmpty

theorem SheafBHistPointGermLedger_restriction_readback
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
            hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  cases sameOpen
  have restrictedOpenUnary : UnaryHistory openHist := ledger.right.left
  have sameGerm : hsame germ restrictedGerm :=
    cont_deterministic ledger.right.right restrictedRow
  exact And.intro
    (And.intro ledger.left (And.intro restrictedOpenUnary restrictedRow))
    sameGerm

theorem SheafBHistPointGermLedger_identity_open_membership_cont_exactness
    {point openHist sectionHist germ : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ↔
      ∃ memberOpen : BHist, hsame memberOpen openHist ∧
        Cont memberOpen sectionHist germ ∧
          SheafBHistPointGermLedger point memberOpen sectionHist germ := by
  constructor
  · intro ledger
    exact Exists.intro openHist
      (And.intro (hsame_refl openHist)
        (And.intro ledger.right.right ledger))
  · intro witness
    cases witness with
    | intro memberOpen data =>
        cases data.left
        exact data.right.right

theorem SheafBHistPointGermLedger_refinement_composition
    {point openA openB openC sectionHist germA germB germC : BHist} :
    SheafBHistPointGermLedger point openA sectionHist germA ->
      hsame openA openB ->
        Cont openB sectionHist germB ->
          hsame openB openC ->
            Cont openC sectionHist germC ->
              SheafBHistPointGermLedger point openC sectionHist germC ∧
                hsame germA germC ∧ hsame germB germC := by
  intro ledger sameAB rowB sameBC rowC
  have readbackB :
      SheafBHistPointGermLedger point openB sectionHist germB ∧ hsame germA germB :=
    SheafBHistPointGermLedger_restriction_readback ledger sameAB rowB
  have readbackC :
      SheafBHistPointGermLedger point openC sectionHist germC ∧ hsame germB germC :=
    SheafBHistPointGermLedger_restriction_readback readbackB.left sameBC rowC
  exact And.intro readbackC.left
    (And.intro (hsame_trans readbackB.right readbackC.right) readbackC.right)

theorem SheafRestrictedOpenCarrier_semantic_name_certificate
    {point openHist sectionHist germ : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        hsame := by
  intro ledger
  constructor
  · constructor
    · exact Exists.intro germ ledger
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (cont_result_hsame_transport carrier.right.right same))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

theorem SheafRestrictedOpenCarrier_restriction_laws
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          UnaryHistory point ∧ UnaryHistory restrictedOpen ∧
            Cont restrictedOpen sectionHist restrictedGerm ∧ hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  cases sameOpen
  have sameGerm : hsame germ restrictedGerm :=
    cont_deterministic ledger.right.right restrictedRow
  exact And.intro ledger.left
    (And.intro ledger.right.left
      (And.intro restrictedRow sameGerm))

theorem SheafBHistPointGermLedger_gluing_readback
    {point openHist sect germ memberOpen memberSect memberGerm : BHist} :
    SheafBHistPointGermLedger point openHist sect germ ->
      UnaryHistory memberOpen -> hsame openHist memberOpen -> hsame sect memberSect ->
        Cont memberOpen memberSect memberGerm ->
          SheafBHistPointGermLedger point memberOpen memberSect memberGerm ∧
            hsame germ memberGerm := by
  intro ledger memberOpenUnary sameOpen sameSect memberRow
  cases sameOpen
  cases sameSect
  have sameGerm : hsame germ memberGerm :=
    cont_deterministic ledger.right.right memberRow
  exact And.intro
    (And.intro ledger.left (And.intro memberOpenUnary memberRow))
    sameGerm

theorem SheafBHistPointGermComparison_trans
    {point openA openB openC sectA sectB sectC germA germB germC common : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      SheafBHistPointGermComparison point openB sectB germB openC sectC germC common ->
        SheafBHistPointGermComparison point openA sectA germA openC sectC germC common := by
  intro first second
  exact And.intro first.left
    (And.intro first.right.left
      (And.intro second.right.right.left
        (And.intro first.right.right.right.left
          (And.intro first.right.right.right.right.left
            (And.intro second.right.right.right.right.right.left
              (And.intro first.right.right.right.right.right.right.left
                (And.intro second.right.right.right.right.right.right.right.left
                  (hsame_trans first.right.right.right.right.right.right.right.right
                    second.right.right.right.right.right.right.right.right))))))))

theorem SheafBHistPointGermComparison_symmetric_fields
    {point openA openB sectA sectB germA germB common : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      UnaryHistory point ∧ UnaryHistory openB ∧ UnaryHistory openA ∧ UnaryHistory common ∧
        hsame common openB ∧ hsame common openA ∧ Cont common sectB germB ∧
          Cont common sectA germA ∧ hsame germB germA := by
  intro comparison
  exact And.intro comparison.left
    (And.intro comparison.right.right.left
      (And.intro comparison.right.left
        (And.intro comparison.right.right.right.left
          (And.intro comparison.right.right.right.right.right.left
            (And.intro comparison.right.right.right.right.left
                (And.intro comparison.right.right.right.right.right.right.right.left
                  (And.intro comparison.right.right.right.right.right.right.left
                    (hsame_symm comparison.right.right.right.right.right.right.right.right))))))))

theorem SheafBHistPointGermComparison_soundness
    {point openA openB sectA sectB germA germB common globalA globalB : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      Cont common sectA globalA -> Cont common sectB globalB ->
        hsame germA globalA -> hsame germB globalB -> hsame globalA globalB := by
  intro comparison _globalACont _globalBCont sameGlobalA sameGlobalB
  exact hsame_trans (hsame_symm sameGlobalA)
    (hsame_trans comparison.right.right.right.right.right.right.right.right sameGlobalB)

theorem SheafBHistPointGermLedger_common_open_comparison
    {point openHist sectA sectB germA germB : BHist} :
    SheafBHistPointGermLedger point openHist sectA germA ->
      SheafBHistPointGermLedger point openHist sectB germB ->
        hsame germA germB ->
          SheafBHistPointGermComparison point openHist sectA germA openHist sectB germB
              openHist ∧
            Cont openHist sectA germA ∧ Cont openHist sectB germB := by
  intro ledgerA ledgerB sameGerm
  have openCommon : UnaryHistory openHist := ledgerA.right.left
  have comparison :
      SheafBHistPointGermComparison point openHist sectA germA openHist sectB germB
        openHist :=
    And.intro ledgerA.left
      (And.intro ledgerA.right.left
        (And.intro ledgerB.right.left
          (And.intro openCommon
            (And.intro (hsame_refl openHist)
              (And.intro (hsame_refl openHist)
                (And.intro ledgerA.right.right
                  (And.intro ledgerB.right.right sameGerm)))))))
  exact And.intro comparison (And.intro ledgerA.right.right ledgerB.right.right)

theorem SheafBHistPointGermLedger_shared_open_classifier_transitivity
    {point openA openB openC sectionA sectionB sectionC germA germB germC : BHist} :
    SheafBHistPointGermLedger point openA sectionA germA ->
      SheafBHistPointGermLedger point openB sectionB germA ->
        SheafBHistPointGermLedger point openB sectionB germB ->
          SheafBHistPointGermLedger point openC sectionC germB ->
            UnaryHistory sectionC -> Cont openA sectionC germC ->
              SheafBHistPointGermLedger point openA sectionC germC ∧
                hsame germA germB ∧ UnaryHistory germC := by
  intro rowA sharedA sharedB _rowC sectionCUnary directAC
  have sameAB : hsame germA germB :=
    cont_deterministic sharedA.right.right sharedB.right.right
  have germCUnary : UnaryHistory germC :=
    unary_cont_closed rowA.right.left sectionCUnary directAC
  exact And.intro
    (And.intro rowA.left (And.intro rowA.right.left directAC))
    (And.intro sameAB germCUnary)

theorem SheafRestrictedOpenCarrier_locality_gluing_descent
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have readbackA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen restrictedA
  have readbackB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen restrictedB
  have sameRestrictedA : hsame restrictedGermA germA := hsame_symm readbackA.right
  have sameRestrictedB : hsame germB restrictedGermB := readbackB.right
  exact And.intro readbackA.left
    (And.intro readbackB.left
      (hsame_trans sameRestrictedA (hsame_trans sameGerm sameRestrictedB)))

def SheafDownstreamConsumerScope
    (point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionA germA ∧
    SheafBHistPointGermLedger point openHist sectionB germB ∧
      hsame germA germB ∧ hsame openHist restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB ∧
            hsame chartEndpoint restrictedGermB

theorem SheafDownstreamConsumer_carrier_scope
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint ->
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame chartEndpoint restrictedGermB := by
  intro scope
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      scope.left scope.right.left scope.right.right.left scope.right.right.right.left
      scope.right.right.right.right.left scope.right.right.right.right.right.left
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro scope.right.right.right.right.left
        (And.intro scope.right.right.right.right.right.left
          (And.intro descent.right.right scope.right.right.right.right.right.right))))

theorem SheafBHistPointGermComparison_restricted_open_descent
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :=
    SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right
  exact comparison.left

theorem SheafIdentityCover_gluing_collapse
    {point openHist sectionA sectionB globalA globalB localGerm : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistPointGermLedger point openHist sectionA globalA ->
        SheafBHistPointGermLedger point openHist sectionB globalB ->
          Cont openHist sectionA localGerm ->
            Cont openHist sectionB localGerm ->
              hsame globalA globalB ∧
                SheafBHistPointGermLedger point openHist sectionA localGerm ∧
                  SheafBHistPointGermLedger point openHist sectionB localGerm := by
  intro openPoint ledgerA ledgerB localA localB
  have sameGlobalLocalA : hsame globalA localGerm :=
    cont_deterministic ledgerA.right.right localA
  have sameGlobalLocalB : hsame globalB localGerm :=
    cont_deterministic ledgerB.right.right localB
  have sameGlobal : hsame globalA globalB :=
    hsame_trans sameGlobalLocalA (hsame_symm sameGlobalLocalB)
  have pointUnary : UnaryHistory point :=
    unary_transport unary_empty (hsame_symm openPoint.right)
  exact And.intro sameGlobal
    (And.intro
      (And.intro pointUnary (And.intro ledgerA.right.left localA))
      (And.intro pointUnary (And.intro ledgerB.right.left localB)))

theorem SheafBHistPointGermLedger_restricted_global_soundness
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA -> Cont restrictedOpen sectionB globalB ->
                hsame restrictedGermA globalA ∧ hsame restrictedGermB globalB ∧
                  hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalRowA globalRowB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have sameGlobalA : hsame restrictedGermA globalA :=
    cont_deterministic restrictedA globalRowA
  have sameGlobalB : hsame restrictedGermB globalB :=
    cont_deterministic restrictedB globalRowB
  exact And.intro sameGlobalA
    (And.intro sameGlobalB
      (hsame_trans (hsame_symm sameGlobalA)
        (hsame_trans descent.right.right sameGlobalB)))

theorem SheafBHistPointGermComparison_restricted_global_soundness
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  hsame restrictedGermA globalA ->
                    hsame restrictedGermB globalB -> hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
    sameGlobalA sameGlobalB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  exact SheafBHistPointGermComparison_soundness
    comparison globalACont globalBCont sameGlobalA sameGlobalB

theorem SheafBHistPointGermLedger_route_cont_composition
    {point openA routeAB openB routeBC openC routeAC openC' sect germC germC' : BHist} :
    SheafBHistPointGermLedger point openC sect germC ->
      Cont openA routeAB openB -> Cont openB routeBC openC ->
        Cont routeAB routeBC routeAC -> Cont openA routeAC openC' ->
          Cont openC' sect germC' ->
            SheafBHistPointGermLedger point openC' sect germC' ∧
              hsame openC openC' ∧ hsame germC germC' := by
  intro ledger routeA routeB routeAB routeDirect sectionDirect
  have sameOpen : hsame openC openC' :=
    cont_assoc_relational routeA routeB routeAB routeDirect
  have openUnary : UnaryHistory openC' :=
    unary_transport ledger.right.left sameOpen
  have sameGerm : hsame germC germC' :=
    cont_respects_hsame sameOpen (hsame_refl sect) ledger.right.right sectionDirect
  exact And.intro
    (And.intro ledger.left (And.intro openUnary sectionDirect))
    (And.intro sameOpen sameGerm)

theorem SheafRootCoverDescent_common_refinement_germ_exactness
    {point openA openB sectA sectB germA germB common globalA globalB : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      Cont common sectA globalA -> Cont common sectB globalB -> hsame germA globalA ->
        hsame germB globalB ->
          SheafBHistPointGermComparison point openA sectA globalA openB sectB globalB
            common ∧
            hsame globalA globalB := by
  intro comparison globalACont globalBCont sameGlobalA sameGlobalB
  have sameGlobal :
      hsame globalA globalB :=
    SheafBHistPointGermComparison_soundness
      comparison globalACont globalBCont sameGlobalA sameGlobalB
  exact And.intro
    (And.intro comparison.left
      (And.intro comparison.right.left
        (And.intro comparison.right.right.left
          (And.intro comparison.right.right.right.left
            (And.intro comparison.right.right.right.right.left
              (And.intro comparison.right.right.right.right.right.left
                (And.intro globalACont
                  (And.intro globalBCont sameGlobal))))))))
    sameGlobal

theorem SheafRootRingedSpaceLocalRingProjection_seal
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA restrictedGermB
      tail : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                  SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                    hsame restrictedGermA restrictedGermB ∧
                      (hsame restrictedOpen (BHist.e0 tail) -> False) := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right).left
  have restrictedOpenNotZero : hsame restrictedOpen (BHist.e0 tail) -> False := by
    intro sameZero
    exact unary_no_zero_extension (unary_transport descent.left.right.left sameZero)
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro comparison
        (And.intro descent.right.right restrictedOpenNotZero)))

theorem SheafBHistPointGermLedger_route_history_stability
    {point openHist sectionHist germ restrictedOpen route routeTarget restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen route routeTarget ->
          hsame routeTarget restrictedOpen ->
            Cont routeTarget sectionHist restrictedGerm ->
              hsame route BHist.Empty ∧
                SheafBHistPointGermLedger point routeTarget sectionHist restrictedGerm ∧
                  hsame germ restrictedGerm := by
  intro ledger sameOpen routeRow sameTarget restrictedRow
  have routeEmpty : hsame route BHist.Empty :=
    cont_right_unit_unique (cont_result_hsame_transport routeRow sameTarget)
  have routeTargetUnary : UnaryHistory routeTarget := by
    cases sameOpen
    exact unary_transport ledger.right.left (hsame_symm sameTarget)
  have sameOpenRouteTarget : hsame openHist routeTarget :=
    hsame_trans sameOpen (hsame_symm sameTarget)
  have sameGerm : hsame germ restrictedGerm :=
    cont_respects_hsame sameOpenRouteTarget (hsame_refl sectionHist)
      ledger.right.right restrictedRow
  exact And.intro routeEmpty
    (And.intro
      (And.intro ledger.left (And.intro routeTargetUnary restrictedRow))
      sameGerm)

theorem SheafBHistPointGermLedger_cover_descent_exhaustion
    {point openHist sectA sectB germA germB memberOpen memberSectA memberSectB
      memberGermA memberGermB common commonGermA commonGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectA germA ->
      SheafBHistPointGermLedger point openHist sectB germB ->
        hsame germA germB -> hsame openHist memberOpen -> hsame sectA memberSectA ->
          hsame sectB memberSectB -> Cont memberOpen memberSectA memberGermA ->
            Cont memberOpen memberSectB memberGermB -> hsame memberOpen common ->
              Cont common memberSectA commonGermA ->
                Cont common memberSectB commonGermB ->
                  SheafBHistPointGermComparison point common memberSectA commonGermA
                      common memberSectB commonGermB common ∧
                    hsame germA commonGermA ∧ hsame germB commonGermB := by
  intro ledgerA ledgerB sameGerm sameMemberOpen sameSectA sameSectB memberRowA memberRowB
    sameCommon commonRowA commonRowB
  have memberOpenUnary : UnaryHistory memberOpen := by
    cases sameMemberOpen
    exact ledgerA.right.left
  have memberReadbackA :
      SheafBHistPointGermLedger point memberOpen memberSectA memberGermA ∧
        hsame germA memberGermA :=
    SheafBHistPointGermLedger_gluing_readback ledgerA memberOpenUnary sameMemberOpen
      sameSectA memberRowA
  have memberReadbackB :
      SheafBHistPointGermLedger point memberOpen memberSectB memberGermB ∧
        hsame germB memberGermB :=
    SheafBHistPointGermLedger_gluing_readback ledgerB memberOpenUnary sameMemberOpen
      sameSectB memberRowB
  have commonReadbackA :
      SheafBHistPointGermLedger point common memberSectA commonGermA ∧
        hsame memberGermA commonGermA :=
    SheafBHistPointGermLedger_restriction_readback memberReadbackA.left sameCommon commonRowA
  have commonReadbackB :
      SheafBHistPointGermLedger point common memberSectB commonGermB ∧
        hsame memberGermB commonGermB :=
    SheafBHistPointGermLedger_restriction_readback memberReadbackB.left sameCommon commonRowB
  have sameCommonGerms : hsame commonGermA commonGermB :=
    hsame_trans (hsame_symm commonReadbackA.right)
      (hsame_trans (hsame_symm memberReadbackA.right)
        (hsame_trans sameGerm
          (hsame_trans memberReadbackB.right commonReadbackB.right)))
  have comparison :
      SheafBHistPointGermComparison point common memberSectA commonGermA common memberSectB
        commonGermB common :=
    (SheafBHistPointGermLedger_common_open_comparison
      commonReadbackA.left commonReadbackB.left sameCommonGerms).left
  exact And.intro comparison
    (And.intro
      (hsame_trans memberReadbackA.right commonReadbackA.right)
      (hsame_trans memberReadbackB.right commonReadbackB.right))

end BEDC.Derived.SheafUp
