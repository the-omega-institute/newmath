import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMembraneUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def AuditMembraneCarrier (G B R D H P N : BHist) : Prop :=
  UnaryHistory G ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory P ∧
    hsame H (append G B) ∧ Cont G B R ∧ Cont R D N

theorem AuditMembraneCarrier_refusal_replay_closure {G B R D H P N : BHist} :
    AuditMembraneCarrier G B R D H P N →
      UnaryHistory R ∧ UnaryHistory N ∧ hsame H (append G B) := by
  intro packet
  have unaryG : UnaryHistory G :=
    packet.left
  have unaryB : UnaryHistory B :=
    packet.right.left
  have unaryD : UnaryHistory D :=
    packet.right.right.left
  have sameAuditFace : hsame H (append G B) :=
    packet.right.right.right.right.left
  have refusalRoute : Cont G B R :=
    packet.right.right.right.right.right.left
  have replayRoute : Cont R D N :=
    packet.right.right.right.right.right.right
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryG unaryB refusalRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryR unaryD replayRoute
  exact ⟨unaryR, unaryN, sameAuditFace⟩

theorem AuditMembraneCarrier_drift_resolution {G B R D H P N drift : BHist} :
    AuditMembraneCarrier G B R D H P N →
      Cont D P drift →
        UnaryHistory D ∧ UnaryHistory P ∧ UnaryHistory drift ∧ Cont D P drift ∧
          hsame H (append G B) ∧ Cont R D N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet driftRoute
  have unaryD : UnaryHistory D :=
    packet.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.left
  have sameAuditFace : hsame H (append G B) :=
    packet.right.right.right.right.left
  have replayRoute : Cont R D N :=
    packet.right.right.right.right.right.right
  have unaryDrift : UnaryHistory drift :=
    unary_cont_closed unaryD unaryP driftRoute
  exact ⟨unaryD, unaryP, unaryDrift, driftRoute, sameAuditFace, replayRoute⟩

theorem AuditMembraneCarrier_namecert_obligations {G B R D H P N : BHist} :
    AuditMembraneCarrier G B R D H P N →
      SemanticNameCert
          (fun row : BHist => AuditMembraneCarrier G B R D H P N ∧ hsame row N)
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist => hsame row N ∧ hsame H (append G B))
          hsame ∧
        UnaryHistory R ∧ UnaryHistory N ∧ hsame H (append G B) := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame UnaryHistory Cont
  intro carrier
  have closure := AuditMembraneCarrier_refusal_replay_closure carrier
  have unaryN : UnaryHistory N := closure.right.left
  have sameAuditFace : hsame H (append G B) := closure.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist => AuditMembraneCarrier G B R D H P N ∧ hsame row N)
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist => hsame row N ∧ hsame H (append G B))
          hsame := by
    constructor
    · constructor
      · exact Exists.intro N ⟨carrier, hsame_refl N⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, unary_transport unaryN (hsame_symm source.right)⟩
    · intro row source
      exact ⟨source.right, sameAuditFace⟩
  exact ⟨cert, closure.left, unaryN, sameAuditFace⟩

theorem AuditMembraneCarrier_consumer_boundary {G B R D H P N consumer : BHist} :
    AuditMembraneCarrier G B R D H P N →
      Cont N P consumer →
        UnaryHistory G ∧ UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory D ∧
          UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory consumer ∧
            hsame H (append G B) ∧ Cont G B R ∧ Cont R D N ∧
              Cont N P consumer := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet consumerRoute
  have closure := AuditMembraneCarrier_refusal_replay_closure packet
  have unaryG : UnaryHistory G := packet.left
  have unaryB : UnaryHistory B := packet.right.left
  have unaryD : UnaryHistory D := packet.right.right.left
  have unaryP : UnaryHistory P := packet.right.right.right.left
  have sameAuditFace : hsame H (append G B) := closure.right.right
  have refusalRoute : Cont G B R := packet.right.right.right.right.right.left
  have replayRoute : Cont R D N := packet.right.right.right.right.right.right
  have unaryR : UnaryHistory R := closure.left
  have unaryN : UnaryHistory N := closure.right.left
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryN unaryP consumerRoute
  exact
    ⟨unaryG, unaryB, unaryR, unaryD, unaryP, unaryN, unaryConsumer, sameAuditFace,
      refusalRoute, replayRoute, consumerRoute⟩

theorem AuditMembraneUp_StdBridge {G B R D H P N exported : BHist} :
    AuditMembraneCarrier G B R D H P N →
      Cont N P exported →
        SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist => Cont N P row ∧ hsame H (append G B))
          (fun row : BHist => hsame row exported ∧ Cont G B R ∧ Cont R D N)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier exportRoute
  have closure := AuditMembraneCarrier_refusal_replay_closure carrier
  have unaryP : UnaryHistory P :=
    carrier.right.right.right.left
  have unaryN : UnaryHistory N :=
    closure.right.left
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed unaryN unaryP exportRoute
  have sameAuditFace : hsame H (append G B) :=
    closure.right.right
  have refusalRoute : Cont G B R :=
    carrier.right.right.right.right.right.left
  have replayRoute : Cont R D N :=
    carrier.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited := Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm source.left),
          sameAuditFace⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, replayRoute⟩
  }

end BEDC.Derived.AuditMembraneUp
