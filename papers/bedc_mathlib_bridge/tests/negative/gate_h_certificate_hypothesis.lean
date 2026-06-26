namespace BedcMathlibBridge.Negative

structure HollowCertificate where
  witness : Nat
  evidence : witness = witness

theorem hollow_certificate_exists (cert : HollowCertificate) :
    ∃ n : Nat, n = n :=
  ⟨cert.witness, cert.evidence⟩

end BedcMathlibBridge.Negative
