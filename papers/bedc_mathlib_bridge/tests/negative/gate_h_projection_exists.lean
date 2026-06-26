namespace BedcMathlibBridge.Negative

structure HollowPayload where
  witness : Nat
  evidence : witness = witness

theorem hollow_projection_exists (payload : HollowPayload) :
    ∃ n : Nat, n = n :=
  ⟨payload.witness, payload.evidence⟩

end BedcMathlibBridge.Negative
