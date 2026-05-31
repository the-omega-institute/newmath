import BEDC.Derived.ApartnessTopologyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApartnessTopologyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ApartnessTopologyCarrier (G O T M S W R Q D E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont
  UnaryHistory G ∧ UnaryHistory O ∧ UnaryHistory T ∧ UnaryHistory M ∧
    UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory Q ∧
      UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont G O E ∧ Cont E T H ∧ Cont H C N

theorem ApartnessTopologyCarrier_namecert_obligation_surface
    {G O T M S W R Q D E H C P N localName : BHist} :
    ApartnessTopologyCarrier G O T M S W R Q D E H C P N →
      SemanticNameCert
        (fun row : BHist =>
          ApartnessTopologyCarrier G O T M S W R Q D E H C P N ∧
            hsame row localName)
        (fun row : BHist =>
          ApartnessTopologyCarrier G O T M S W R Q D E H C P N ∧
            hsame row localName)
        (fun row : BHist =>
          ApartnessTopologyCarrier G O T M S W R Q D E H C P N ∧
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame NameCert UnaryHistory
  intro carrier
  constructor
  · constructor
    · exact Exists.intro localName ⟨carrier, hsame_refl localName⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other same
      exact hsame_symm same
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row other same source
      exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
  · intro _row source
    exact source
  · intro _row source
    exact source

end BEDC.Derived.ApartnessTopologyUp
