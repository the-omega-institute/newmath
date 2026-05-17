import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RefutationBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

def RefutationBoundaryCarrier (A F D S T H C P N : BHist) : Prop :=
  Cont A F D ∧
    hsame A A ∧
      hsame F F ∧
        hsame D D ∧
          hsame S S ∧
            hsame T T ∧
              hsame H H ∧
                hsame C C ∧
                  hsame P P ∧ hsame N N ∧ msame BMark.b0 BMark.b0

def RefutationBoundaryObligationSurface (A F D S T H C P N : BHist) : Prop :=
  RefutationBoundaryCarrier A F D S T H C P N ∧
    Cont A F D ∧
      hsame A A ∧
        hsame F F ∧
          hsame D D ∧
            hsame S S ∧
              hsame T T ∧
                hsame H H ∧
                  hsame C C ∧
                    hsame P P ∧ hsame N N ∧ msame BMark.b1 BMark.b1

theorem RefutationBoundaryCarrier_namecert_obligation_surface
    {A F D S T H C P N : BHist}
    (carrier : RefutationBoundaryCarrier A F D S T H C P N)
    (route : Cont A F D) :
    RefutationBoundaryObligationSurface A F D S T H C P N ∧
      SemanticNameCert
        (fun h : BHist => RefutationBoundaryCarrier A F D S T H C P h)
        (fun h : BHist => RefutationBoundaryCarrier A F D S T H C P h)
        (fun h : BHist => RefutationBoundaryCarrier A F D S T H C P h)
        (fun h k : BHist => hsame h k) := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame SemanticNameCert
  constructor
  · constructor
    · exact carrier
    · constructor
      · exact route
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · rfl
                  · constructor
                    · rfl
                    · constructor
                      · rfl
                      · constructor
                        · rfl
                        · rfl
  · exact {
      core := {
        carrier_inhabited := Exists.intro N carrier
        equiv_refl := by
          intro h _source
          rfl
        equiv_symm := by
          intro h k same
          exact same.symm
        equiv_trans := by
          intro h k r sameHK sameKR
          exact sameHK.trans sameKR
        carrier_respects_equiv := by
          intro h k same source
          cases same
          exact source
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }

theorem RefutationBoundaryPermittedNegationSound
    {A F D S T H C P N result : BHist}
    (carrier : RefutationBoundaryCarrier A F D S T H C P N)
    (follow : Cont D H result) :
    Cont A F D ∧ Cont D H result ∧ hsame A A ∧ hsame F F ∧ hsame D D ∧
      hsame result result ∧ msame BMark.b0 BMark.b0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame BMark
  obtain ⟨route, sameA, sameF, sameD, _sameS, _sameT, _sameH, _sameC, _sameP,
    _sameN, markSame⟩ := carrier
  exact ⟨route, follow, sameA, sameF, sameD, rfl, markSame⟩

theorem RefutationBoundaryCarrier_permitted_negation_sound {A F D S T H C P N : BHist}
    (carrier : RefutationBoundaryCarrier A F D S T H C P N) (replay : Cont D C P) :
    Cont A (append F C) P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  constructor
  · cases carrier with
    | intro route rest =>
        cases route
        cases replay
        exact append_assoc A F C
  · rfl

theorem RefutationBoundaryCarrier_realup_consumer_scope
    {A F D S T H C P N endpoint : BHist} :
    RefutationBoundaryCarrier A F D S T H C P N →
      Cont D C endpoint →
        Cont A (append F C) endpoint ∧ hsame S S ∧ hsame T T ∧ hsame H H ∧
          hsame P P ∧ hsame N N ∧ msame BMark.b0 BMark.b0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame BMark
  intro carrier endpointRoute
  obtain ⟨route, _sameA, _sameF, _sameD, sameS, sameT, sameH, _sameC, sameP,
    sameN, markSame⟩ := carrier
  have consumerRoute : Cont A (append F C) endpoint := by
    cases route
    exact endpointRoute.trans (append_assoc A F C)
  exact ⟨consumerRoute, sameS, sameT, sameH, sameP, sameN, markSame⟩

theorem RefutationBoundaryForbiddenTruthBranchExclusion
    {A F D S T H C P N tail : BHist}
    (carrier : RefutationBoundaryCarrier A F D S T H C P N) :
    (Cont D (BHist.e0 tail) A → False) ∧
      (Cont D (BHist.e1 tail) A → False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  obtain ⟨route, _sameA, _sameF, _sameD, _sameS, _sameT, _sameH, _sameC,
    _sameP, _sameN, _markSame⟩ := carrier
  exact
    ⟨fun back => cont_mutual_extension_right_tail_absurd.left route back,
      fun back => cont_mutual_extension_right_tail_absurd.right route back⟩

theorem RefutationBoundaryRealUpConsumerScope
    {A F D S T H C P N result : BHist}
    (carrier : RefutationBoundaryCarrier A F D S T H C P N)
    (replay : Cont D C result) :
    SemanticNameCert
      (fun row : BHist => hsame row result)
      (fun row : BHist => hsame row result ∧ Cont A F D ∧ Cont D C result)
      (fun row : BHist =>
        RefutationBoundaryObligationSurface A F D S T H C P N ∧ hsame row result)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have carrierWitness : RefutationBoundaryCarrier A F D S T H C P N := carrier
  obtain ⟨route, sameA, sameF, sameD, sameS, sameT, sameH, sameC, sameP, sameN,
    _markSame⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro result rfl
      equiv_refl := by
        intro _row _source
        rfl
      equiv_symm := by
        intro _row _other same
        exact same.symm
      equiv_trans := by
        intro _row _other _next sameRO sameON
        exact sameRO.trans sameON
      carrier_respects_equiv := by
        intro _row _other same source
        exact same.symm.trans source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source, route, replay⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨⟨carrierWitness, route, sameA, sameF, sameD, sameS, sameT, sameH, sameC,
            sameP, sameN, rfl⟩,
          source⟩
  }

end BEDC.Derived.RefutationBoundaryUp
