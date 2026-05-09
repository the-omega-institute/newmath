import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootPublicThresholdPacket_source_fiber_classifier_determinacy
    {groupSource topologySource product inverse neighbourhood ledger classifier provenance
      classifierRead : BHist} :
    TopGroupRootPublicThresholdPacket groupSource topologySource product inverse neighbourhood
        ledger classifier provenance ->
      Cont ledger classifier classifierRead ->
        SemanticNameCert (fun row : BHist => hsame row classifierRead)
            (fun row : BHist => hsame row classifierRead)
            (fun row : BHist => hsame row classifierRead) hsame ∧
          GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
            hsame classifier ledger ∧ hsame classifierRead (append ledger classifier) ∧
              hsame provenance BHist.Empty := by
  intro packet classifierRow
  have readSelf : hsame classifierRead classifierRead :=
    hsame_refl classifierRead
  have cert :
      SemanticNameCert (fun row : BHist => hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead) hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead readSelf
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.right.right.left
          (And.intro classifierRow packet.right.right.right.right.right))))

end BEDC.Derived.TopGroupUp
