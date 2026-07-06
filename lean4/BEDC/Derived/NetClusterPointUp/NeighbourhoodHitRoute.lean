import BEDC.Derived.NetClusterPointUp.TasteGate
import BEDC.Derived.NetConvergenceUp

namespace BEDC.Derived.NetClusterPointUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NetClusterPoint_neighbourhood_hit_netconvergence_dependency
    {moore directed subnet convergence compact transport replay provenance localName
      source tail entourage optionalSource filter schedule readback realSeal ncTransport
      ncReplay ncProvenance ncName : BHist} :
    BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier source tail entourage
      optionalSource filter schedule readback realSeal ncTransport ncReplay ncProvenance
      ncName ->
      hsame convergence source ->
        Cont source tail entourage ->
          Cont entourage filter schedule ->
            Cont schedule readback realSeal ->
              Cont realSeal ncTransport compact ->
                hsame compact source ->
                  (SemanticNameCert
                      (fun row : BHist =>
                        hsame row compact ∧
                          BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier source tail
                            entourage optionalSource filter schedule readback realSeal
                            ncTransport ncReplay ncProvenance ncName)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row tail ∨ hsame row entourage ∨
                          hsame row filter ∨ hsame row schedule ∨ hsame row readback ∨
                            hsame row realSeal ∨ hsame row compact)
                      (fun row : BHist =>
                        Cont source tail entourage ∧ Cont entourage filter schedule ∧
                          Cont schedule readback realSeal ∧
                            Cont realSeal ncTransport compact ∧ hsame row source)
                      hsame ∧
                    hsame source source ∧ hsame tail tail ∧ hsame entourage entourage ∧
                      hsame filter filter ∧ hsame schedule schedule ∧
                        hsame readback readback ∧ hsame realSeal realSeal) ∧
                    hsame convergence source ∧
                      netClusterPointFields
                          (NetClusterPointUp.mk moore directed subnet convergence compact
                            transport replay provenance localName) =
                        [moore, directed, subnet, convergence, compact, transport, replay,
                          provenance, localName] := by
  -- BEDC touchpoint anchor: NetClusterPointUp NetConvergenceCarrier SemanticNameCert
  intro carrier convergenceSame sourceTail entourageRoute scheduleRoute compactRoute compactSame
  have dependency :=
    BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier_sequentialcompact_dependency
      (D := source)
      (T := tail)
      (E := entourage)
      (A := optionalSource)
      (F := filter)
      (S := schedule)
      (R := readback)
      (L := realSeal)
      (H := ncTransport)
      (C := ncReplay)
      (P := ncProvenance)
      (M := ncName)
      (clusterRead := compact)
      carrier sourceTail entourageRoute scheduleRoute compactRoute compactSame
  exact ⟨dependency, convergenceSame, rfl⟩

theorem NetClusterPoint_entourage_tail_stability_consumer
    {moore directed subnet convergence compact transport replay provenance localName
      source tail entourage optionalSource filter schedule readback realSeal ncTransport
      ncReplay ncProvenance ncName source' tail' entourage' optionalSource' filter'
      schedule' readback' realSeal' ncTransport' ncReplay' ncProvenance' ncName'
      handoff handoff' : BHist} :
    BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier source tail entourage
      optionalSource filter schedule readback realSeal ncTransport ncReplay ncProvenance
      ncName ->
      BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier source' tail' entourage'
        optionalSource' filter' schedule' readback' realSeal' ncTransport' ncReplay'
        ncProvenance' ncName' ->
        hsame source source' ->
          hsame tail tail' ->
            hsame entourage entourage' ->
              hsame filter filter' ->
                Cont source tail entourage ->
                  Cont source' tail' entourage' ->
                    Cont entourage filter handoff ->
                      Cont entourage' filter' handoff' ->
                        hsame compact source ->
                          (hsame handoff handoff' ∧ Cont source tail entourage ∧
                              Cont source' tail' entourage' ∧
                                Cont entourage filter handoff ∧
                                  Cont entourage' filter' handoff') ∧
                            hsame compact source ∧
                              netClusterPointFields
                                  (NetClusterPointUp.mk moore directed subnet convergence compact
                                    transport replay provenance localName) =
                                [moore, directed, subnet, convergence, compact, transport,
                                  replay, provenance, localName] := by
  -- BEDC touchpoint anchor: NetClusterPointUp NetConvergenceCarrier entourage stability
  intro carrier carrier' sameSource sameTail sameEntourage sameFilter sourceTail
    sourceTail' handoffRoute handoffRoute' compactSame
  have stable :=
    BEDC.Derived.NetConvergenceUp.NetConvergenceCarrier_entourage_tail_stability
      (D := source)
      (T := tail)
      (E := entourage)
      (A := optionalSource)
      (F := filter)
      (S := schedule)
      (R := readback)
      (L := realSeal)
      (H := ncTransport)
      (C := ncReplay)
      (P := ncProvenance)
      (M := ncName)
      (D' := source')
      (T' := tail')
      (E' := entourage')
      (A' := optionalSource')
      (F' := filter')
      (S' := schedule')
      (R' := readback')
      (L' := realSeal')
      (H' := ncTransport')
      (C' := ncReplay')
      (P' := ncProvenance')
      (M' := ncName')
      (handoff := handoff)
      (handoff' := handoff')
      carrier carrier' sameSource sameTail sameEntourage sameFilter sourceTail sourceTail'
      handoffRoute handoffRoute'
  obtain ⟨sameHandoff, _sameSource, _sameSource', sourceTailStable, sourceTailStable',
    handoffStable, handoffStable'⟩ := stable
  exact
    ⟨⟨sameHandoff, sourceTailStable, sourceTailStable', handoffStable, handoffStable'⟩,
      compactSame, rfl⟩

end BEDC.Derived.NetClusterPointUp
