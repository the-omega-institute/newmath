import BEDC.FKernel.Cont
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

end BEDC.Derived.ObserverKernelTraceUp
