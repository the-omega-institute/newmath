import BEDC.Derived.SocketKindClassifierUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SocketKindClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SocketKindClassifierNameCertObligations (x : SocketKindClassifierUp) :
    ∃ socket kind requested gate transports routes provenance nameCert : BHist,
      x = SocketKindClassifierUp.mk socket kind requested gate transports routes provenance
        nameCert ∧
        SemanticNameCert
          (fun row : BHist => hsame row nameCert)
          (fun row : BHist =>
            hsame row socket ∨ hsame row kind ∨ hsame row requested ∨ hsame row gate ∨
              hsame row transports ∨ hsame row routes ∨ hsame row provenance ∨
                hsame row nameCert)
          (fun row : BHist => hsame row provenance ∨ hsame row nameCert)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk socket kind requested gate transports routes provenance nameCert =>
      exact
        ⟨socket, kind, requested, gate, transports, routes, provenance, nameCert, rfl,
          {
            core := {
              carrier_inhabited := ⟨nameCert, hsame_refl nameCert⟩
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
                exact hsame_trans (hsame_symm sameRows) source
            }
            pattern_sound := by
              intro row source
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
            ledger_sound := by
              intro row source
              exact Or.inr source
          }⟩

end BEDC.Derived.SocketKindClassifierUp
