import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ObserverKernelTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

inductive ObserverKernelTraceUp : Type where
  | mk :
      (trace transport route probe signature ledger provenance localName : BHist) →
        ObserverKernelTraceUp

theorem ObserverKernelTraceNameCert_obligations
    {trace transport route probe signature ledger provenance localName replay : BHist}
    (traceReplay : Cont trace ledger route) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row trace ∧
          ∃ packet : ObserverKernelTraceUp,
            packet =
              ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
                localName)
      (fun row : BHist =>
        hsame row trace ∧ hsame probe probe ∧ hsame signature signature ∧ hsame ledger ledger)
      (fun row : BHist =>
        Cont trace ledger route ∧ hsame row trace ∧ hsame provenance provenance ∧
          hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  refine
    { core :=
        { carrier_inhabited := ?carrier
          equiv_refl := ?refl
          equiv_symm := ?symm
          equiv_trans := ?trans
          carrier_respects_equiv := ?respects }
      pattern_sound := ?pattern
      ledger_sound := ?ledger }
  · exact
      Exists.intro trace
        (And.intro (hsame_refl trace)
          (Exists.intro
            (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
              localName)
            rfl))
  · intro h _source
    exact hsame_refl h
  · intro h k same
    exact hsame_symm same
  · intro h k r sameHK sameKR
    exact hsame_trans sameHK sameKR
  · intro h k sameHK source
    exact
      And.intro (hsame_trans (hsame_symm sameHK) source.left)
        (Exists.intro
          (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
            localName)
          rfl)
  · intro h source
    exact
      And.intro source.left
        (And.intro (hsame_refl probe)
          (And.intro (hsame_refl signature) (hsame_refl ledger)))
  · intro h source
    exact
      And.intro traceReplay
        (And.intro source.left
          (And.intro (hsame_refl provenance) (hsame_refl localName)))

theorem ObserverKernelTrace_non_escape
    {trace transport route probe signature ledger provenance localName consumer subjectTail : BHist}
    (traceReplay : Cont trace ledger route)
    (consumerRoute : Cont route provenance consumer) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row trace ∧
            ∃ packet : ObserverKernelTraceUp,
              packet =
                ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
                  localName)
        (fun row : BHist =>
          hsame row trace ∧ hsame probe probe ∧ hsame signature signature ∧
            hsame ledger ledger)
        (fun row : BHist =>
          Cont trace ledger route ∧ hsame row trace ∧ hsame provenance provenance ∧
            hsame localName localName)
        hsame ∧
      Cont route provenance consumer ∧
        (Cont consumer (BHist.e0 subjectTail) route → False) ∧
          (Cont consumer (BHist.e1 subjectTail) route → False) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  exact
    ⟨ObserverKernelTraceNameCert_obligations
        (trace := trace) (transport := transport) (route := route) (probe := probe)
        (signature := signature) (ledger := ledger) (provenance := provenance)
        (localName := localName) (replay := trace) traceReplay,
      consumerRoute,
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.left consumerRoute subjectReturn),
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.right consumerRoute subjectReturn)⟩

theorem ObserverKernelTrace_no_subject_non_escape
    {trace transport route probe signature ledger provenance localName subjectRead : BHist}
    (traceReplay : Cont trace ledger route)
    (ledgerReplay : Cont ledger localName subjectRead) :
    SemanticNameCert
      (fun row : BHist =>
        (∃ packet : ObserverKernelTraceUp,
          packet =
            ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
              localName) ∧
          hsame row subjectRead)
      (fun row : BHist =>
        hsame row subjectRead ∧ Cont trace ledger route ∧ Cont ledger localName subjectRead)
      (fun row : BHist =>
        hsame row subjectRead ∧ hsame provenance provenance ∧ hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  refine
    { core :=
        { carrier_inhabited := ?carrier
          equiv_refl := ?refl
          equiv_symm := ?symm
          equiv_trans := ?trans
          carrier_respects_equiv := ?respects }
      pattern_sound := ?pattern
      ledger_sound := ?ledger }
  · exact
      Exists.intro subjectRead
        (And.intro
          (Exists.intro
            (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
              localName)
            rfl)
          (hsame_refl subjectRead))
  · intro h _source
    exact hsame_refl h
  · intro h k same
    exact hsame_symm same
  · intro h k r sameHK sameKR
    exact hsame_trans sameHK sameKR
  · intro h k sameHK source
    exact
      And.intro
        (Exists.intro
          (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
            localName)
          rfl)
        (hsame_trans (hsame_symm sameHK) source.right)
  · intro h source
    exact And.intro source.right (And.intro traceReplay ledgerReplay)
  · intro h source
    exact
      And.intro source.right
        (And.intro (hsame_refl provenance) (hsame_refl localName))

theorem ObserverKernelTrace_public_export_boundary
    {trace transport route probe signature ledger provenance localName consumer : BHist}
    (traceReplay : Cont trace ledger route)
    (consumerRoute : Cont route provenance consumer) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row consumer ∧
          ∃ packet : ObserverKernelTraceUp,
            packet =
              ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
                localName)
      (fun row : BHist =>
        Cont trace ledger route ∧ Cont route provenance consumer ∧ hsame row consumer ∧
          hsame probe probe ∧ hsame signature signature)
      (fun row : BHist =>
        hsame row consumer ∧ hsame ledger ledger ∧ hsame provenance provenance ∧
          hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  refine
    { core :=
        { carrier_inhabited := ?carrier
          equiv_refl := ?refl
          equiv_symm := ?symm
          equiv_trans := ?trans
          carrier_respects_equiv := ?respects }
      pattern_sound := ?pattern
      ledger_sound := ?ledger }
  · exact
      Exists.intro consumer
        (And.intro (hsame_refl consumer)
          (Exists.intro
            (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
              localName)
            rfl))
  · intro row _source
    exact hsame_refl row
  · intro row row' sameRows
    exact hsame_symm sameRows
  · intro row row' row'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row row' sameRows source
    exact
      And.intro (hsame_trans (hsame_symm sameRows) source.left)
        (Exists.intro
          (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
            localName)
          rfl)
  · intro row source
    exact
      And.intro traceReplay
        (And.intro consumerRoute
          (And.intro source.left
            (And.intro (hsame_refl probe) (hsame_refl signature))))
  · intro row source
    exact
      And.intro source.left
        (And.intro (hsame_refl ledger)
          (And.intro (hsame_refl provenance) (hsame_refl localName)))

theorem ObserverKernelTrace_public_bridge_route
    {trace transport route probe signature ledger provenance localName consumer bridgeRead : BHist}
    (traceReplay : Cont trace ledger route)
    (consumerRoute : Cont route provenance consumer)
    (bridgeRoute : Cont consumer localName bridgeRead) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row bridgeRead ∧
          ∃ packet : ObserverKernelTraceUp,
            packet =
              ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
                localName)
      (fun row : BHist =>
        Cont trace ledger route ∧ Cont route provenance consumer ∧
          Cont consumer localName bridgeRead ∧ hsame row bridgeRead ∧ hsame probe probe ∧
            hsame signature signature)
      (fun row : BHist =>
        hsame row bridgeRead ∧ hsame ledger ledger ∧ hsame provenance provenance ∧
          hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  refine
    { core :=
        { carrier_inhabited := ?carrier
          equiv_refl := ?refl
          equiv_symm := ?symm
          equiv_trans := ?trans
          carrier_respects_equiv := ?respects }
      pattern_sound := ?pattern
      ledger_sound := ?ledger }
  · exact
      Exists.intro bridgeRead
        (And.intro (hsame_refl bridgeRead)
          (Exists.intro
            (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
              localName)
            rfl))
  · intro row _source
    exact hsame_refl row
  · intro row row' sameRows
    exact hsame_symm sameRows
  · intro row row' row'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row row' sameRows source
    exact
      And.intro (hsame_trans (hsame_symm sameRows) source.left)
        (Exists.intro
          (ObserverKernelTraceUp.mk trace transport route probe signature ledger provenance
            localName)
          rfl)
  · intro row source
    exact
      And.intro traceReplay
        (And.intro consumerRoute
          (And.intro bridgeRoute
            (And.intro source.left
              (And.intro (hsame_refl probe) (hsame_refl signature)))))
  · intro row source
    exact
      And.intro source.left
        (And.intro (hsame_refl ledger)
          (And.intro (hsame_refl provenance) (hsame_refl localName)))

end BEDC.Derived.ObserverKernelTraceUp
